; define-fun after check-sat returns the solver to assert mode, where get-assignment is an error
; (cvc5, z3 4.6 and later, yices2 and SMTInterpol answer it; their adapters check)
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (! p :named a))
(check-sat)
(define-fun r () Bool true)
(get-assignment)
