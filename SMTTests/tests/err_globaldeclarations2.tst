; checks global declarations
(set-logic QF_UF)
(declare-fun a () Bool)
(reset-assertions)
(assert a)  ; not yet defined - ERROR
