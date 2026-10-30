; OPTIONS: --solver z3-4.14.1 -T 60
; A solver that exits silently before its whole-run limit has passed is not reported as timed out.
(set-logic QF_UF)
(declare-fun p () Bool)
