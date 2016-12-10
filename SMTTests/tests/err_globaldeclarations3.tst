; checks global declarations
(set-option :global-declarations true)
(set-logic QF_UF)
(declare-fun a () Bool)
(reset)
(get-option :global-declarations) ; should be false
(assert a)  ; not defined - ERROR
