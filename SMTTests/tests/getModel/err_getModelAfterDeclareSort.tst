; declare-sort after check-sat returns the solver to assert mode, where get-model is an error
; (z3 4.6 and later, yices2, SMTInterpol and Bitwuzla answer it; their adapters check)
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(declare-sort S 0)
(get-model)
