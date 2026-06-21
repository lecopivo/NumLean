#!/usr/bin/env bash

IGNORE_FILE="importignore"

mv .gitignore .gitignore_backup
cp importignore .gitignore

emit_imports() {
    while read -r file; do
        # Check if the file is ignored based on importignore
        if [[ -f "$IGNORE_FILE" ]] && git check-ignore --no-index -q "$file"; then
            echo "-- import ${file%.lean}" | sed 's,/,.,g'
            continue  # Skip ignored files
        fi
        # Format the import statement
        echo "import ${file%.lean}" | sed 's,/,.,g'
    done
}

# Find all non-experimental Lean files in NumLean/
find NumLean \
    -path 'NumLean/Experimental' -prune -o \
    -type f -name '*.lean' -print | LC_ALL=C sort | emit_imports > NumLean.lean

# Find all experimental Lean files in NumLean/Experimental/
find NumLean/Experimental -type f -name '*.lean' | LC_ALL=C sort | emit_imports > NumLeanExperimental.lean

cat > NumLeanAll.lean <<'EOF'
import NumLean
import NumLeanExperimental
EOF

# Find all Lean files in Tests/
find Tests -type f -name '*.lean' | LC_ALL=C sort | while read -r file; do
    # Check if the file is ignored based on importignore
    if [[ -f "$IGNORE_FILE" ]] && git check-ignore --no-index -q "$file"; then
        echo "-- import ${file%.lean}" | sed 's,/,.,g'
        continue  # Skip ignored files
    fi
    # Format the import statement
    echo "import ${file%.lean}" | sed 's,/,.,g'
done > Tests.lean

cat >> Tests.lean <<'EOF'

def main : IO Unit := do
  pure ()
EOF


mv .gitignore_backup .gitignore
