; tests define-fun
(set-logic QF_UF)
(declare-sort A 0)
(declare-fun a () A)
(define-fun x () A a)
(define-fun y ((p A)(q A)) Bool false)
(assert (y x x))
