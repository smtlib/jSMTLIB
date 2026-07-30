; tests define-fun
(set-logic QF_UF)
(define-fun x () Bool true)
(define-fun y ((p Bool)(q Bool)) Bool (and p q))
(assert (y x x))
