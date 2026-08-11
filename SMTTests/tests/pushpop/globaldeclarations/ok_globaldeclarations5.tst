; checks global declarations
(set-option :global-declarations false)
(set-logic QF_UF)
(declare-fun a () Bool)
(reset-assertions) ; removes declaration
(declare-fun a () Bool) ; OK
(check-sat)  ; sat
