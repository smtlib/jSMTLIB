; define-fun after check-sat returns the solver to assert mode, where get-value is an error
; (cvc5, z3 4.6 and later, yices2 and SMTInterpol answer it; their adapters check)
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(define-fun r () Bool true)
(get-value (p))
