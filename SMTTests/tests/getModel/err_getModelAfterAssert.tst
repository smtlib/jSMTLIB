; assert after check-sat returns the solver to assert mode, where get-model is an error
; (cvc5 answers it; its adapter checks)
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(assert true)
(get-model)
