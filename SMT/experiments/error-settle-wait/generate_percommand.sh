#!/usr/bin/env bash
# Builds a single .smt2 file of N iterations, each consisting of K trivial
# "filler" declare-fun commands followed by one check-sat, joined by (reset),
# ending in (exit). No assertions are made, so check-sat is trivially fast
# regardless of K -- this isolates the marginal cost of sending more
# individual commands (jSMTLIB dispatches each one separately and waits for
# its response) from any actual solving cost, to test whether jSMTLIB's
# per-iteration overhead scales with the number of commands per iteration.
#
# Usage: ./generate_percommand.sh K N outputFile
set -euo pipefail

K="$1"
N="$2"
OUT="$3"

: > "$OUT"
for ((i = 0; i < N; i++)); do
    echo "(set-logic QF_LIA)" >> "$OUT"
    for ((j = 0; j < K; j++)); do
        echo "(declare-fun filler$j () Bool)" >> "$OUT"
    done
    echo "(check-sat)" >> "$OUT"
    if (( i < N - 1 )); then
        echo "(reset)" >> "$OUT"
    else
        echo "(exit)" >> "$OUT"
    fi
done
