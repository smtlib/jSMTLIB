; QF_IDL restricts = and distinct over Int to the atom shapes (op x y), (op (- x y) n) and
; (op (- x y) (- n)); an Int-sorted ite is not an atom argument; atoms are binary, so a
; chained (= x y y) is rejected too
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(declare-const p Bool)
(assert (= x (* 3 y)))
(assert (= (+ x y) 7))
(assert (distinct x 3))
(assert (< x (ite p y x)))
(assert (= x y y))
