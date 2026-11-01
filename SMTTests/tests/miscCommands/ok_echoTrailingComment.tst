; OPTIONS: --relax --solver test --echo
; --echo prints a command without its same-line trailing comment, for an extension command
; as for a standard one; (what) is a Solver_test-only command, hence --solver test
(set-logic QF_UF)
(declare-const c Bool) ; after a standard command
(what c) ; after an extension command
(check-sat) ; last
