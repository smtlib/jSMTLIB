; checks global declarations
(set-option :global-declarations true)
(set-logic QF_UF)
(declare-fun a () Bool)
(reset-assertions) ; does not remove declarations, as they are global
(declare-fun a () Bool) ; duplicate
(check-sat)  ; sat
