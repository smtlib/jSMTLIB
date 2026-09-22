; defining an already defined fun
(set-logic QF_UF)
(define-fun f () Bool true)
(push 1)
(define-fun f () Bool false)
