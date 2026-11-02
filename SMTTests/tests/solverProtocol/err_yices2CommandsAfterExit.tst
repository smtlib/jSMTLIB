; OPTIONS: --solver yices2
; yices2 exits after an error, its declared error behavior. Every later command answers just that the
; solver has exited, including those the adapter checks with its own get-option or answers itself.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(assert q)
(get-value (p))
(get-model)
(get-assignment)
(get-unsat-core)
(echo "hi")
(set-option :print-success true)
(get-option :produce-models)
(get-info :name)
(check-sat)
