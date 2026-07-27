; Tests get-model after check-sat with :produce-models enabled
(set-option :produce-models true)
(set-logic QF_UF)
(check-sat)
(get-model)
