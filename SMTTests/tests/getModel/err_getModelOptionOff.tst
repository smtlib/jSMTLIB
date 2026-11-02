; get-model with :produce-models off is an error (yices2 and SMTInterpol answer it; their
; adapters check)
(set-option :produce-models false)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(get-model)
