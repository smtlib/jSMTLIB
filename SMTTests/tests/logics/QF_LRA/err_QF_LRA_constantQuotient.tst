; Linear arithmetic: a product with a constant quotient is linear; with a zero divisor (on either side) it is not
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* (/ 1 3) x) 1))
(check-sat)
(assert (= y (* (/ 3 0) x)))
(assert (= (* x (/ 1 0)) 1))
