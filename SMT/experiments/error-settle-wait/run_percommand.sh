#!/usr/bin/env bash
# For a fixed solver and N, runs generate_percommand.sh at several K (filler
# command counts) and times both the raw solver and jSMTLIB CLI on each,
# to see whether jSMTLIB's per-iteration time scales with the number of
# commands per iteration (K+2: set-logic, K declare-funs, check-sat, plus a
# trailing reset/exit) or stays flat.
#
# Usage: ./run_percommand.sh [N] [solver] [K1 K2 K3 ...]
set -euo pipefail
cd "$(dirname "$0")"

N="${1:-30}"
SOLVER="${2:-z3-4.16.0}"
shift $(( $# >= 2 ? 2 : $# )) || true
if [ $# -gt 0 ]; then
  KS=("$@")
else
  KS=(0 25 50 100 200)
fi

SMTTESTS_DIR="/Users/davidcok/projects/jSMTLIB/SMTTests"
JAR="/Users/davidcok/projects/jSMTLIB/SMT/jSMTLIB.jar"

if [[ -z "${SMT_SOLVER_DIR:-}" ]]; then
    (cd "$SMTTESTS_DIR" && source setup 2>/dev/null && echo "$SMT_SOLVER_DIR") > /tmp/.smt_solver_dir_rel
    REL=$(cat /tmp/.smt_solver_dir_rel)
    SMT_SOLVER_DIR=$(cd "$SMTTESTS_DIR" && cd "$REL" && pwd)
fi
export SMT_SOLVER_DIR

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

echo "solver=$SOLVER  N=$N  SMT_SOLVER_DIR=$SMT_SOLVER_DIR"
echo "----"

cmd=$(raw_cmd "$SOLVER")

for K in "${KS[@]}"; do
    SCRIPT="/tmp/percommand.$$.$K.smt2"
    ./generate_percommand.sh "$K" "$N" "$SCRIPT"
    cmds_per_iter=$((K + 2))  # set-logic + K declare-funs + check-sat (not counting the reset/exit)

    t0=$(now_s)
    $cmd < "$SCRIPT" > /tmp/raw_out.$$ 2>/tmp/raw_err.$$ || true
    t1=$(now_s)
    raw_secs=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", b-a}')

    t0=$(now_s)
    java -cp "$JAR" org.smtlib.SMT --solver "$SOLVER" --nosuccess "$SCRIPT" > /tmp/jsmtlib_out.$$ 2>/tmp/jsmtlib_err.$$ || true
    t1=$(now_s)
    jsmtlib_secs=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", b-a}')

    printf "K=%-5s cmds/iter=%-5s raw_per_iter_ms=%8.2f jsmtlib_per_iter_ms=%8.2f overhead_per_iter_ms=%8.2f overhead_per_cmd_ms=%7.3f\n" \
        "$K" "$cmds_per_iter" \
        "$(awk -v s="$raw_secs" -v n="$N" 'BEGIN{printf "%.2f", 1000*s/n}')" \
        "$(awk -v s="$jsmtlib_secs" -v n="$N" 'BEGIN{printf "%.2f", 1000*s/n}')" \
        "$(awk -v r="$raw_secs" -v j="$jsmtlib_secs" -v n="$N" 'BEGIN{printf "%.2f", 1000*(j-r)/n}')" \
        "$(awk -v r="$raw_secs" -v j="$jsmtlib_secs" -v n="$N" -v c="$cmds_per_iter" 'BEGIN{printf "%.3f", 1000*(j-r)/n/c}')"

    rm -f "$SCRIPT" /tmp/raw_out.$$ /tmp/raw_err.$$ /tmp/jsmtlib_out.$$ /tmp/jsmtlib_err.$$
done
