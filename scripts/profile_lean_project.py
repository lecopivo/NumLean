#!/usr/bin/env python3

import argparse
import concurrent.futures
import datetime as dt
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from math import sqrt
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[1]
DEFAULT_ROOTS = [Path("NumLean.lean"), Path("Tests.lean")]
DEFAULT_OUT = Path("perf/profile-data/latest.json")
DEFAULT_LOG_DIR = Path("perf/profile-data/logs")
DEFAULT_HISTORY = Path("perf/history.jsonl")

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_'.]+)\s*$")
TOOK_RE = re.compile(r"^(?P<name>.*?)\s+took\s+(?P<value>[0-9]+(?:\.[0-9]+)?)(?P<unit>ns|us|µs|ms|s)\s*$")
PROFILE_LINE_RE = re.compile(r"^\s*(?P<name>.*?)\s+(?P<value>[0-9]+(?:\.[0-9]+)?)(?P<unit>ns|us|µs|ms|s)\s*$")


@dataclass(frozen=True)
class CommandResult:
    command: list[str]
    exit_code: int | None
    timed_out: bool
    duration_s: float
    stdout: str
    stderr: str


def rel(path: Path) -> str:
    return path.relative_to(REPO).as_posix()


def module_to_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def file_to_module(path: Path) -> str:
    return path.with_suffix("").as_posix().replace("/", ".")


def read_imports(path: Path) -> list[str]:
    modules: list[str] = []
    for line in (REPO / path).read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            modules.append(match.group(1))
    return modules


def discover_files(roots: list[Path], recursive: bool) -> list[Path]:
    seen_modules: set[str] = set()
    seen_files: set[Path] = set()
    pending = list(roots)

    for root in roots:
        if (REPO / root).is_file():
            seen_files.add(root)

    while pending:
        file = pending.pop(0)
        path = REPO / file
        if not path.is_file():
            continue
        for module in read_imports(file):
            if module in seen_modules:
                continue
            seen_modules.add(module)
            module_path = module_to_path(module)
            if (REPO / module_path).is_file():
                seen_files.add(module_path)
                if recursive:
                    pending.append(module_path)

    return sorted(seen_files, key=lambda p: p.as_posix())


def run_command(command: list[str], timeout: float | None) -> CommandResult:
    started = time.perf_counter()
    try:
        proc = subprocess.run(
            command,
            cwd=REPO,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
        return CommandResult(
            command=command,
            exit_code=proc.returncode,
            timed_out=False,
            duration_s=time.perf_counter() - started,
            stdout=proc.stdout,
            stderr=proc.stderr,
        )
    except subprocess.TimeoutExpired as exc:
        return CommandResult(
            command=command,
            exit_code=None,
            timed_out=True,
            duration_s=time.perf_counter() - started,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )


def run_stdout(command: list[str]) -> str | None:
    try:
        proc = subprocess.run(command, cwd=REPO, text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def time_to_seconds(value: str, unit: str) -> float:
    number = float(value)
    if unit == "s":
        return number
    if unit == "ms":
        return number / 1_000
    if unit in {"us", "µs"}:
        return number / 1_000_000
    if unit == "ns":
        return number / 1_000_000_000
    return number


def category_of(name: str) -> str:
    if name.startswith("typeclass inference"):
        return "typeclass inference"
    if name.startswith("interpretation"):
        return "interpretation"
    if name.startswith("compilation"):
        return "compilation"
    return name.split(" of ", 1)[0].strip() or name


def grouped_entries(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    groups: dict[tuple[str, str], list[float]] = {}
    for entry in entries:
        key = (entry["name"], entry["category"])
        groups.setdefault(key, []).append(entry["seconds"])

    out: list[dict[str, Any]] = []
    for (name, category), values in groups.items():
        count = len(values)
        total = sum(values)
        mean = total / count
        variance = sum((value - mean) ** 2 for value in values) / count
        out.append(
            {
                "name": name,
                "category": category,
                "count": count,
                "seconds": total,
                "total_seconds": total,
                "min_seconds": min(values),
                "max_seconds": max(values),
                "mean_seconds": mean,
                "stddev_seconds": sqrt(variance),
            }
        )
    out.sort(key=lambda item: (item["total_seconds"], item["max_seconds"]), reverse=True)
    return out


def parse_profile_output(text: str, limit: int) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    cumulative: dict[str, float] = {}
    categories: dict[str, float] = {}
    in_cumulative = False

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line == "cumulative profiling times:":
            in_cumulative = True
            continue

        if in_cumulative:
            match = PROFILE_LINE_RE.match(line)
            if match:
                cumulative[match.group("name")] = time_to_seconds(match.group("value"), match.group("unit"))
                continue
            in_cumulative = False

        match = TOOK_RE.match(line)
        if not match:
            continue

        name = match.group("name").strip()
        seconds = time_to_seconds(match.group("value"), match.group("unit"))
        category = category_of(name)
        categories[category] = categories.get(category, 0.0) + seconds
        entries.append({"name": name, "category": category, "seconds": seconds})

    grouped = grouped_entries(entries)
    return {
        "entries": grouped[:limit],
        "entry_count": len(entries),
        "grouped_entry_count": len(grouped),
        "cumulative": dict(sorted(cumulative.items(), key=lambda kv: kv[1], reverse=True)),
        "categories": dict(sorted(categories.items(), key=lambda kv: kv[1], reverse=True)),
    }


def write_text(path: Path, value: str) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")
    return rel(path)


def result_json(result: CommandResult, stdout_path: Path, stderr_path: Path) -> dict[str, Any]:
    return {
        "command": result.command,
        "exit_code": result.exit_code,
        "timed_out": result.timed_out,
        "duration_s": result.duration_s,
        "stdout_path": write_text(stdout_path, result.stdout),
        "stderr_path": write_text(stderr_path, result.stderr),
        "stdout_bytes": len(result.stdout.encode("utf-8")),
        "stderr_bytes": len(result.stderr.encode("utf-8")),
    }


def profile_file(path: Path, args: argparse.Namespace, log_dir: Path) -> dict[str, Any]:
    safe = path.as_posix().replace("/", "__").replace(".", "_")
    file_log_dir = log_dir / safe
    file_log_dir.mkdir(parents=True, exist_ok=True)
    module = file_to_module(path)

    lean_base = ["lake", "env", "lean", "--root=."]
    normal = run_command([*lean_base, path.as_posix()], args.timeout)
    profiled = run_command(
        ["lake", "env", "lean", "--profile", f"-Dprofiler.threshold={args.profiler_threshold}", "--root=.", path.as_posix()],
        args.timeout,
    )

    trace_path = file_log_dir / "trace-profiler.log"
    detailed = None
    if not args.skip_trace_profiler:
        detailed = run_command(
            [
                "lake",
                "env",
                "lean",
                "-Dtrace.profiler=true",
                f"-Dtrace.profiler.output={trace_path.as_posix()}",
                "--root=.",
                path.as_posix(),
            ],
            args.timeout,
        )

    profile_text = f"{profiled.stdout}\n{profiled.stderr}"
    trace_text = ""
    if detailed is not None:
        trace_text = f"{detailed.stdout}\n{detailed.stderr}"
        if trace_path.is_file():
            try:
                trace_text += "\n" + trace_path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                pass

    data: dict[str, Any] = {
        "path": path.as_posix(),
        "module": module,
        "normal": result_json(normal, file_log_dir / "normal.stdout", file_log_dir / "normal.stderr"),
        "profile": result_json(profiled, file_log_dir / "profile.stdout", file_log_dir / "profile.stderr"),
        "profile_data": parse_profile_output(profile_text, args.max_entries_per_file),
    }
    if detailed is not None:
        data["trace_profiler"] = result_json(detailed, file_log_dir / "trace.stdout", file_log_dir / "trace.stderr")
        if trace_path.is_file():
            data["trace_profiler"]["trace_output_path"] = rel(trace_path)
            data["trace_profiler"]["trace_output_bytes"] = trace_path.stat().st_size
        data["trace_profile_data"] = parse_profile_output(trace_text, args.max_entries_per_file)

    return data


def build_summary(files: list[dict[str, Any]]) -> dict[str, Any]:
    failures = [f for f in files if any((f[key]["exit_code"] not in (0, None) or f[key]["timed_out"]) for key in f if key in {"normal", "profile", "trace_profiler"})]
    slow_normal = sorted(files, key=lambda f: f["normal"]["duration_s"], reverse=True)[:25]
    slow_profile = sorted(files, key=lambda f: f["profile"]["duration_s"], reverse=True)[:25]
    aggregate_categories: dict[str, float] = {}
    aggregate_cumulative: dict[str, float] = {}
    for file in files:
        for category, seconds in file["profile_data"].get("categories", {}).items():
            aggregate_categories[category] = aggregate_categories.get(category, 0.0) + seconds
        for category, seconds in file["profile_data"].get("cumulative", {}).items():
            aggregate_cumulative[category] = aggregate_cumulative.get(category, 0.0) + seconds
    return {
        "file_count": len(files),
        "failure_count": len(failures),
        "slowest_normal": [{"path": f["path"], "seconds": f["normal"]["duration_s"]} for f in slow_normal],
        "slowest_profile": [{"path": f["path"], "seconds": f["profile"]["duration_s"]} for f in slow_profile],
        "profile_categories": dict(sorted(aggregate_categories.items(), key=lambda kv: kv[1], reverse=True)),
        "profile_cumulative": dict(sorted(aggregate_cumulative.items(), key=lambda kv: kv[1], reverse=True)),
    }


def file_status(file: dict[str, Any]) -> int:
    for key in ["normal", "profile", "trace_profiler"]:
        result = file.get(key)
        if result and (result.get("timed_out") or result.get("exit_code") != 0):
            return 1
    return 0


def write_history(report: dict[str, Any], history_path: Path, relative_threshold: float, absolute_threshold_s: float) -> None:
    cumulative_names = sorted(
        {
            name
            for file in report.get("files", [])
            for name in file.get("profile_data", {}).get("cumulative", {}).keys()
        }
    )
    metrics = ["normal", "profile", "status", *cumulative_names]
    rows = []
    for file in sorted(report.get("files", []), key=lambda item: item["path"]):
        cumulative = file.get("profile_data", {}).get("cumulative", {})
        rows.append(
            [
                file["path"],
                round(file["normal"]["duration_s"], 6),
                round(file["profile"]["duration_s"], 6),
                file_status(file),
                *[round(cumulative.get(name, 0.0), 6) for name in cumulative_names],
            ]
        )

    entry = {
        "schema": 1,
        "timestamp": report.get("metadata", {}).get("finished_at"),
        "git": run_stdout(["git", "rev-parse", "--short", "HEAD"]),
        "lean": run_stdout(["lake", "env", "lean", "--short-version"]),
        "threshold": {"relative": relative_threshold, "absolute_s": absolute_threshold_s},
        "metrics": metrics,
        "files": rows,
    }
    history_path.parent.mkdir(parents=True, exist_ok=True)
    with history_path.open("a", encoding="utf-8") as out:
        out.write(json.dumps(entry, separators=(",", ":")))
        out.write("\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Collect Lean elaboration performance data for NumLean.")
    parser.add_argument("--compact-existing", type=Path, help="compact an existing report instead of running Lean")
    parser.add_argument("--root", action="append", type=Path, dest="roots", help="aggregate Lean file to read imports from; can be passed multiple times")
    parser.add_argument("--recursive", action="store_true", help="also follow imports inside imported local files")
    parser.add_argument("--skip-build", action="store_true", help="do not run lake build before profiling")
    parser.add_argument("--build-target", action="append", dest="build_targets", help="Lake target to build first; defaults to NumLean and Tests")
    parser.add_argument("--jobs", type=int, default=1, help="number of Lean files to elaborate concurrently; default is intentionally 1")
    parser.add_argument("--timeout", type=float, default=None, help="per-command timeout in seconds")
    parser.add_argument("--limit", type=int, default=None, help="only profile the first N discovered files")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUT, help="JSON output path")
    parser.add_argument("--log-dir", type=Path, default=DEFAULT_LOG_DIR, help="directory for raw stdout/stderr logs")
    parser.add_argument("--history", type=Path, default=DEFAULT_HISTORY, help="JSONL history file for compact trend data")
    parser.add_argument("--no-history", action="store_true", help="do not append a compact history entry")
    parser.add_argument("--trend-relative-threshold", type=float, default=0.05, help="relative trend threshold stored in history")
    parser.add_argument("--trend-absolute-threshold", type=float, default=0.1, help="absolute trend threshold in seconds stored in history")
    parser.add_argument("--profiler-threshold", type=int, default=0, help="Lean profiler threshold passed through -Dprofiler.threshold")
    parser.add_argument("--max-entries-per-file", type=int, default=200, help="maximum parsed profiler entries stored per file")
    parser.add_argument("--skip-trace-profiler", action="store_true", help="skip the extra trace.profiler run")
    return parser.parse_args()


def compact_report(path: Path, output: Path, max_entries: int) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    for file in data.get("files", []):
        for key in ["profile_data", "trace_profile_data"]:
            profile_data = file.get(key)
            if not profile_data:
                continue
            entries = profile_data.get("entries", [])
            if entries and "count" not in entries[0]:
                entries = grouped_entries(entries)
            entries = entries[:max_entries]
            for entry in entries:
                entry.pop("line", None)
            profile_data["entries"] = entries
            profile_data.setdefault("grouped_entry_count", len(entries))
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, indent=2), encoding="utf-8")


def main() -> int:
    args = parse_args()
    args.jobs = max(1, args.jobs)
    roots = args.roots or DEFAULT_ROOTS
    build_targets = args.build_targets or ["NumLean", "Tests"]
    output = (REPO / args.output).resolve()
    log_dir = (REPO / args.log_dir).resolve()
    history_path = (REPO / args.history).resolve()

    if args.compact_existing is not None:
        compact_report((REPO / args.compact_existing).resolve(), output, args.max_entries_per_file)
        print(f"wrote compacted report to {rel(output)}", flush=True)
        return 0

    files = discover_files(roots, args.recursive)
    if args.limit is not None:
        files = files[: args.limit]
    if not files:
        print("no Lean files found from aggregate imports", file=sys.stderr)
        return 2

    run_started = dt.datetime.now(dt.UTC).isoformat()
    build = None
    if not args.skip_build:
        print(f"building project with lake build {' '.join(build_targets)}", flush=True)
        build_result = run_command(["lake", "build", *build_targets], args.timeout)
        build = result_json(build_result, log_dir / "build.stdout", log_dir / "build.stderr")
        if build_result.exit_code != 0 or build_result.timed_out:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(
                json.dumps(
                    {
                        "metadata": {
                            "started_at": run_started,
                            "finished_at": dt.datetime.now(dt.UTC).isoformat(),
                            "repo": str(REPO),
                            "roots": [r.as_posix() for r in roots],
                            "build_targets": build_targets,
                        },
                        "build": build,
                        "files": [],
                        "summary": {"file_count": len(files), "failure_count": 1},
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            print(f"lake build failed; wrote partial report to {rel(output)}", file=sys.stderr)
            return build_result.exit_code or 1

    print(f"profiling {len(files)} Lean files with jobs={args.jobs}", flush=True)
    results: list[dict[str, Any]] = []
    if args.jobs == 1:
        for index, path in enumerate(files, 1):
            print(f"[{index}/{len(files)}] {path.as_posix()}", flush=True)
            results.append(profile_file(path, args, log_dir))
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            future_to_path = {executor.submit(profile_file, path, args, log_dir): path for path in files}
            for index, future in enumerate(concurrent.futures.as_completed(future_to_path), 1):
                path = future_to_path[future]
                print(f"[{index}/{len(files)}] {path.as_posix()}", flush=True)
                results.append(future.result())
        results.sort(key=lambda item: item["path"])

    report = {
        "metadata": {
            "started_at": run_started,
            "finished_at": dt.datetime.now(dt.UTC).isoformat(),
            "repo": str(REPO),
            "roots": [r.as_posix() for r in roots],
            "build_targets": build_targets,
            "recursive": args.recursive,
            "jobs": args.jobs,
            "timeout_s": args.timeout,
            "skip_trace_profiler": args.skip_trace_profiler,
            "python": sys.version,
        },
        "build": build,
        "files": results,
        "summary": build_summary(results),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {rel(output)}", flush=True)
    if not args.no_history:
        write_history(report, history_path, args.trend_relative_threshold, args.trend_absolute_threshold)
        print(f"appended {rel(history_path)}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
