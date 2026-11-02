; a declared function is not a term, even with HO-Core (SMT-LIB 2.7 Sec. 3.9, Remark 10);
; wrapped in a lambda it is a map, which = accepts
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)
(assert (= f g))
(assert (= h h))
(assert (= (lambda ((x Int)) (f x)) (lambda ((x Int)) (g x))))
; Solver bugs (.bad goldens): z3 4.8.12 and later accept (= f g), treating functions as
; arrays; yices2 accepts it too (and answers unsat here).
