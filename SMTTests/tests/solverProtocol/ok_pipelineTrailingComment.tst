; OPTIONS: --solver generic --pipeline
; A comment line the solver writes after the last pipelined response (as z3 does after an
; unsupported get-info) is not a response and is not reported as out of step (#214).
; The stub's first reply answers the priming command.
(set-logic QF_UF)
(declare-fun p () Bool)
