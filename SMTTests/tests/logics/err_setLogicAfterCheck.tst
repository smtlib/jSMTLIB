; A second set-logic is an error (SMT-LIB allows set-logic only in start mode) and changes
; nothing: the solver stays in sat mode, so get-value is still checked against :produce-models
; (off here), and the assertion stack keeps p, so the last check is unsat.
(set-option :produce-models false)
(set-logic QF_UF)
(declare-fun p () Bool)
(push 1)
(assert p)
(check-sat)
(set-logic QF_UF)
(get-value (p))
(assert (not p))
(check-sat)
