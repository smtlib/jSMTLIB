; OPTIONS: --solver generic --pipeline
; A comment line the solver writes between pipelined responses is not a response.
; The stub's first reply answers the priming command.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
