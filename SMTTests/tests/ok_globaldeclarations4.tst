; checks global declarations
(set-option :global-declarations true)
(set-logic QF_UF)
(declare-fun a () Bool)
(assert (not a))
(check-sat)
(reset-assertions)
(assert a)
(check-sat)
