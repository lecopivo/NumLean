#!/usr/bin/env bash

IGNORE_FILE="importignore"

mv .gitignore .gitignore_backup
cp importignore .gitignore

# Find all Lean files in NumLean/
find NumLean -type f -name '*.lean' | LC_ALL=C sort | while read -r file; do
    # Check if the file is ignored based on importignore
    if [[ -f "$IGNORE_FILE" ]] && git check-ignore --no-index -q "$file"; then
        echo "-- import ${file%.lean}" | sed 's,/,.,g'
        continue  # Skip ignored files
    fi
    # Format the import statement
    echo "import ${file%.lean}" | sed 's,/,.,g'
done > NumLean.lean

# Find all Lean files in
find Tests -type f -name '*.lean' | LC_ALL=C sort | while read -r file; do
    # Check if the file is ignored based on importignore
    if [[ -f "$IGNORE_FILE" ]] && git check-ignore --no-index -q "$file"; then
        echo "-- import ${file%.lean}" | sed 's,/,.,g'
        continue  # Skip ignored files
    fi
    # Format the import statement
    echo "import ${file%.lean}" | sed 's,/,.,g'
done > Tests.lean



mv .gitignore_backup .gitignore
