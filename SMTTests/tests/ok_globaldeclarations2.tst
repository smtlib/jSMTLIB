; checks global declarations
(set-logic QF_UF)
(declare-fun a () Bool)
(reset-assertions)
(declare-fun a () Bool) ; duplicate
(check-sat)  ; sat
