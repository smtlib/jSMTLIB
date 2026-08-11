; checks global declarations
(set-option :global-declarations true)
(set-logic QF_UF)
(declare-fun a () Bool)
(reset-assertions) ; keeps declaration
(assert a)
(check-sat)  ; sat
