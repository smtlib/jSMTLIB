#!/usr/bin/env bash
# Compares running a big multi-copy SMT-LIB script directly against a raw
# solver binary (bypassing jSMTLIB entirely) vs. running the identical
# script through the jSMTLIB CLI (java -cp jSMTLIB.jar org.smtlib.SMT).
# Both invocations launch their process (and, for jSMTLIB, the JVM) exactly
# once for the whole script, so with N large enough that one-time cost is
# amortized and what's left is dominated by per-command overhead: none for
# the raw solver, jSMTLIB's SMT-LIB parsing/type-checking/dialect-translation
# for the jSMTLIB run.
#
# The raw solver is launched with the exact same command-line flags its
# Solver_*.java adapter uses (see the lookup table below), so the only
# difference being measured is jSMTLIB's own processing layer, not a
# different solver invocation mode.
#
# Usage: ./run_experiment.sh [N] [baseScript] [solver1 solver2 ...]
set -euo pipefail
cd "$(dirname "$0")"

N="${1:-50}"
BASE="${2:-bv16.smt2}"
shift $(( $# >= 2 ? 2 : $# )) || true
if [ $# -gt 0 ]; then
  SOLVERS=("$@")
else
  SOLVERS=(z3-4.16.0 cvc5-1.3.2 yices2-2.7.0 smtinterpol-2.5)
fi

SMTTESTS_DIR="/Users/davidcok/projects/jSMTLIB/SMTTests"
JAR="/Users/davidcok/projects/jSMTLIB/SMT/jSMTLIB.jar"

if [[ -z "${SMT_SOLVER_DIR:-}" ]]; then
    (cd "$SMTTESTS_DIR" && source setup 2>/dev/null && echo "$SMT_SOLVER_DIR") > /tmp/.smt_solver_dir_rel
    REL=$(cat /tmp/.smt_solver_dir_rel)
    SMT_SOLVER_DIR=$(cd "$SMTTESTS_DIR" && cd "$REL" && pwd)
fi
export SMT_SOLVER_DIR

BIGSCRIPT="/tmp/bigscript.$$.smt2"
trap 'rm -f "$BIGSCRIPT"' EXIT
./generate_bigscript.sh "$N" "$BASE" "$BIGSCRIPT"

echo "N=$N  base=$BASE  SMT_SOLVER_DIR=$SMT_SOLVER_DIR"
echo "----"

# Raw-invocation flags, copied from each solver's Solver_*.java cmds_mac
# array (macOS), so the raw run uses the identical solver invocation mode
# jSMTLIB itself uses -- interactive/incremental stdin-driven, not batch-file.
raw_cmd() {
    case "$1" in
        z3-*)          echo "$SMT_SOLVER_DIR/$1 -smt2 -in SMTLIB2_COMPLIANT=true WARNING=false" ;;
        cvc5-*)        echo "$SMT_SOLVER_DIR/$1 --lang smt --interactive --incremental --quiet --print-success --strict-parsing" ;;
        yices2-*)      echo "$SMT_SOLVER_DIR/$1 --incremental --interactive" ;;
        smtinterpol-*) echo "java -jar $SMT_SOLVER_DIR/$1.jar -q" ;;
        *) echo "Unknown solver: $1" >&2; exit 1 ;;
    esac
}

now_s() { echo "$EPOCHREALTIME"; }  # macOS's BSD `date` doesn't support %N

for s in "${SOLVERS[@]}"; do
    cmd=$(raw_cmd "$s")

    t0=$(now_s)
    $cmd < "$BIGSCRIPT" > /tmp/raw_out.$$ 2>/tmp/raw_err.$$ || true
    t1=$(now_s)
    raw_secs=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", b-a}')
    raw_sat=$(grep -c '^sat$' /tmp/raw_out.$$ || true)

    t0=$(now_s)
    java -cp "$JAR" org.smtlib.SMT --solver "$s" --nosuccess "$BIGSCRIPT" > /tmp/jsmtlib_out.$$ 2>/tmp/jsmtlib_err.$$ || true
    t1=$(now_s)
    jsmtlib_secs=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", b-a}')
    jsmtlib_sat=$(grep -c '^sat$' /tmp/jsmtlib_out.$$ || true)

    printf "solver=%-16s N=%-5s raw_total_s=%8s raw_per_iter_ms=%8.2f raw_sat_count=%-4s || jsmtlib_total_s=%8s jsmtlib_per_iter_ms=%8.2f jsmtlib_sat_count=%-4s\n" \
        "$s" "$N" "$raw_secs" "$(awk -v s="$raw_secs" -v n="$N" 'BEGIN{printf "%.2f", 1000*s/n}')" "$raw_sat" \
        "$jsmtlib_secs" "$(awk -v s="$jsmtlib_secs" -v n="$N" 'BEGIN{printf "%.2f", 1000*s/n}')" "$jsmtlib_sat"

    rm -f /tmp/raw_out.$$ /tmp/raw_err.$$ /tmp/jsmtlib_out.$$ /tmp/jsmtlib_err.$$
done
