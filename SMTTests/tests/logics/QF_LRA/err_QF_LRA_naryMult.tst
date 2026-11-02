; QF_LRA: a product of any arity is linear only if at most one factor is not a coefficient,
; and a quotient only if all its arguments are; the first three assertions are rejected
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* x y 2.0)))
(assert (= y (* 2.0 x y)))
(assert (= y (/ x 2 3)))
(assert (= y (* 2.0 x 3)))
