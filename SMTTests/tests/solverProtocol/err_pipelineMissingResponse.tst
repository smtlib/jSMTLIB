; OPTIONS: --solver generic --pipeline
; #149: a solver that omits a response: assert gets the 'sat' meant for check-sat, which is out of
; step, and check-sat gets none.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
