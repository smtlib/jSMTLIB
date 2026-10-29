; Under ALL, Simplify decides uninterpreted functions, arrays and linear integer arithmetic.
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(assert (= (select (store a x (f 2)) x) (+ (f 2) (* 2 1))))
(check-sat)
