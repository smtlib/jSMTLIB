; OPTIONS: --solver generic --pipeline
; #149: a solver that writes one response too many: the check-sat gets a 'success', which is out
; of step, and the 'sat' left over is reported. The stub's first reply answers the priming command.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
