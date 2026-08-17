#!/usr/bin/env bash
# Builds a single .smt2 file consisting of N copies of a base script joined by
# (reset), with a final (exit) -- one big script that amortizes solver-launch
# (and, for jSMTLIB, JVM-startup) cost across N solves instead of paying it
# once per solve, so the two invocation modes compared by run_experiment.sh
# can each launch their process exactly once for the whole batch.
#
# Usage: ./generate_bigscript.sh N baseFile outputFile
set -euo pipefail

N="$1"
BASE="$2"
OUT="$3"

: > "$OUT"
for ((i = 0; i < N; i++)); do
    cat "$BASE" >> "$OUT"
    echo "(reset)" >> "$OUT"
done
# Replace the last (reset) with (exit): both invocation modes need the script
# to end deterministically -- the raw solver so it exits on its own once stdin
# is exhausted rather than sitting on EOF from an interactive-mode read loop,
# and jSMTLIB so SMT.exec()'s command loop (which stops at the first (exit)
# or EOD) doesn't need to fall through to EOD handling either.
sed -i '' '$ s/^(reset)$/(exit)/' "$OUT" 2>/dev/null || sed -i '$ s/^(reset)$/(exit)/' "$OUT"
