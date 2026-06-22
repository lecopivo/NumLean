#!/usr/bin/env bash
set -euo pipefail

found=0

while IFS= read -r -d '' file; do
    if ! awk '
        /^[[:space:]]*import[[:space:]]+NumLean[.]Experimental([[:space:].]|$)/ {
            printf "%s:%d: %s\n", FILENAME, FNR, $0
            found = 1
        }
        END { exit found ? 1 : 0 }
    ' "$file"; then
        found=1
    fi
done < <(find NumLean -path 'NumLean/Experimental' -prune -o -type f -name '*.lean' -print0)

if [[ "$found" -ne 0 ]]; then
    printf '\nNon-experimental NumLean files must not import NumLean.Experimental modules.\n' >&2
    printf 'Move the dependency out of Experimental or keep the importing file under NumLean/Experimental/.\n' >&2
    exit 1
fi
