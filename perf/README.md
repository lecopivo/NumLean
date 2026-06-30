# NumLean Performance Profiling

Collect data:

```bash
scripts/profile_lean_project.py
```

The collector runs `lake build NumLean Tests` first, then profiles only the Lean files imported by `NumLean.lean` and `Tests.lean`. It runs sequentially by default to avoid parallel elaborations skewing timing data.

Useful options:

```bash
scripts/profile_lean_project.py --skip-build --limit 5
scripts/profile_lean_project.py --timeout 120
scripts/profile_lean_project.py --jobs 2
scripts/profile_lean_project.py --skip-trace-profiler
scripts/profile_lean_project.py --build-target NumLean --build-target Tests
scripts/profile_lean_project.py --no-history
```

View results:

```bash
python3 -m http.server -d perf 8000
```

Then open <http://localhost:8000/>.

Detailed generated data is written to `perf/profile-data/latest.json`, with raw logs under `perf/profile-data/logs/`. These files are ignored by git and are meant for local inspection.

Each full run also appends a compact historical entry to `perf/history.jsonl`. This file stores per-file normal/profile times, status, and cumulative profiler metrics using a compact column schema. It is intended to be committed and published with GitHub Pages.

The viewer works in two modes:

- With `perf/profile-data/latest.json`: detailed local mode with grouped profiler entries and log popups.
- With only `perf/history.jsonl`: public history mode with the same Files table and thresholded trend columns.

Trend indicators use both thresholds stored in the history entry: relative change defaults to `5%`, and absolute change defaults to `100ms`. Changes below either threshold are shown as stable.
