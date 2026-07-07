#!/usr/bin/env bash
set -euo pipefail

IGNORE_FILE="importignore"

restore_gitignore() {
    if [[ -f .gitignore_backup ]]; then
        mv .gitignore_backup .gitignore
    elif [[ -n "${CREATED_GITIGNORE:-}" ]]; then
        rm -f .gitignore
    fi
}

if [[ -f .gitignore ]]; then
    mv .gitignore .gitignore_backup
else
    CREATED_GITIGNORE=1
fi
trap restore_gitignore EXIT
cp "$IGNORE_FILE" .gitignore

emit_imports() {
    while read -r file; do
        if [[ "$(sed -n '1p' "$file")" != "module" ]]; then
            echo "-- public import ${file%.lean}" | sed 's,/,.,g'
            continue
        fi
        # Check if the file is ignored based on importignore
        if [[ -f "$IGNORE_FILE" ]] && git check-ignore --no-index -q "$file"; then
            echo "-- public import ${file%.lean}" | sed 's,/,.,g'
            continue  # Skip ignored files
        fi
        # Format the import statement
        echo "public import ${file%.lean}" | sed 's,/,.,g'
    done
}

emit_module_imports() {
    echo "module"
    echo
    emit_imports
}

emit_public_section() {
    echo "@[expose] public section"
    echo
}

write_aggregate_imports() {
    local aggregate_file="$1"
    local aggregate_dir="${aggregate_file%.lean}"

    if [[ ! -d "$aggregate_dir" ]]; then
        return
    fi

    find "$aggregate_dir" -type f -name '*.lean' | LC_ALL=C sort | emit_module_imports > "$aggregate_file"
    emit_public_section >> "$aggregate_file"
}

# Find all non-experimental Lean files in NumLean/
find NumLean \
    -path 'NumLean/Experimental' -prune -o \
    -type f -name '*.lean' -print | LC_ALL=C sort | emit_module_imports > NumLean.lean
emit_public_section >> NumLean.lean

# Any `Foo.lean` with a sibling `Foo/` directory is treated as a local aggregate module.
find NumLean \
    -path 'NumLean/Experimental' -prune -o \
    -type f -name '*.lean' -print | while read -r file; do
    write_aggregate_imports "$file"
done

# Find all experimental Lean files in NumLean/Experimental/
find NumLean/Experimental -type f -name '*.lean' | LC_ALL=C sort | emit_module_imports > NumLeanExperimental.lean
emit_public_section >> NumLeanExperimental.lean

find NumLean/Experimental -type f -name '*.lean' -print | while read -r file; do
    write_aggregate_imports "$file"
done

cat > NumLeanAll.lean <<'EOF'
module

public import NumLean
public import NumLeanExperimental

@[expose] public section
EOF

# Find all Lean files in Tests/
find Tests -type f -name '*.lean' | LC_ALL=C sort | emit_module_imports > Tests.lean

cat >> Tests.lean <<'EOF'

@[expose] public section

def main : IO Unit := do
  IO.println "tests done!"
EOF
