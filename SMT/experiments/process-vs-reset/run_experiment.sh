#!/bin/bash
# Runs TimingExperiment across all configured real solvers.
# Usage: ./run_experiment.sh [N] [scriptFile] [solver1 solver2 ...]
#   N          - repetitions per approach per solver (default: 20)
#   scriptFile - SMT-LIB script to repeat (default: default.smt2, a trivial QF_LIA sat instance)
#   solvers    - space-separated solver names (default: the real solvers used by SMTTests)
set -euo pipefail
cd "$(dirname "$0")"

N="${1:-20}"
SCRIPT="${2:-default.smt2}"
shift $(( $# >= 2 ? 2 : $# )) || true
if [ $# -gt 0 ]; then
  SOLVERS=("$@")
else
  SOLVERS=(z3-4.3 z3-4.8.12 z3-4.10.2 z3-4.12.6 z3-4.14.1 z3-4.16.0 cvc5-1.3.2 smtinterpol-2.5 yices2-2.6.5 yices2-2.7.0)
fi

SMTTESTS_DIR="/Users/davidcok/projects/jSMTLIB/SMTTests"
JAR="/Users/davidcok/projects/jSMTLIB/SMT/jSMTLIB.jar"

# Resolve SMT_SOLVER_DIR to an absolute path (relative paths break once we cd elsewhere).
if [[ -z "${SMT_SOLVER_DIR:-}" ]]; then
    (cd "$SMTTESTS_DIR" && source setup 2>/dev/null && echo "$SMT_SOLVER_DIR") > /tmp/.smt_solver_dir_rel
    REL=$(cat /tmp/.smt_solver_dir_rel)
    SMT_SOLVER_DIR=$(cd "$SMTTESTS_DIR" && cd "$REL" && pwd)
fi
export SMT_SOLVER_DIR

echo "N=$N  script=$SCRIPT  SMT_SOLVER_DIR=$SMT_SOLVER_DIR"
echo "----"

javac -cp "$JAR" -d . TimingExperiment.java

for s in "${SOLVERS[@]}"; do
    java -cp "$JAR:." TimingExperiment "$s" "$N" "$SCRIPT"
done
