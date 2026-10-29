; reset-assertions after check-sat returns the solver to assert mode, where get-model is an error
; (cvc5 and z3 4.8 and later answer it; their adapters check)
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(reset-assertions)
(get-model)
