; test scope of define-fun
(set-logic QF_UF)
(define-fun x () Bool true)
(push 1)
(define-fun y () Bool false)
(pop 1)
(assert y)
