; OPTIONS: --solver generic --pipeline
; #149: a response of the wrong shape (sat for declare-fun) is out of step.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
