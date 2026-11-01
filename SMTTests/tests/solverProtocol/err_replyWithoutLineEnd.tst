; OPTIONS: --solver generic
; The solver writes its last reply without a line end and closes its output: the reply still
; answers check-sat, and the command after it learns that the solver has exited.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
