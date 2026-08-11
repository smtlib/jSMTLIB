; checks global declarations
(set-option :global-declarations true)
(set-logic QF_UF)
(declare-fun a () Bool)
(reset)
(get-option :global-declarations) ; Should be false
(set-logic QF_UF)
(declare-fun a () Bool) ; OK - previous declaration cleared
(check-sat) ; sat
