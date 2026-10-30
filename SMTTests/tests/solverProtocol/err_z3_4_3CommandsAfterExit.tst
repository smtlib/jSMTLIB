; OPTIONS: --solver z3-4.3
; As err_yices2CommandsAfterExit.tst, for the z3-4.3 adapter, which sends commands and its own
; get-option queries by its own means.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
(get-model)
(get-assignment)
(get-assertions)
(get-option :produce-models)
(assert p)
(push 1)
(check-sat)
