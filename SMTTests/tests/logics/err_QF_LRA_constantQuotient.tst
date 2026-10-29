; Linear arithmetic: a product with a constant quotient is linear; with a zero divisor it is not
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (= (* (/ 1 3) x) 1))
(check-sat)
(assert (= (* x (/ 1 0)) 1))
