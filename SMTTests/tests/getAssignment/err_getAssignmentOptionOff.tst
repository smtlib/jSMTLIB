; get-assignment with :produce-assignments off is an error, :produce-models notwithstanding
; (cvc5, z3 and yices2 answer it; their adapters check)
(set-option :produce-models true)
(set-option :produce-assignments false)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (! p :named a))
(check-sat)
(get-assignment)
