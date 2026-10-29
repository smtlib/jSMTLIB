; QF_LIA: a product of any arity is linear only if at most one factor is not a coefficient,
; so the first two assertions are rejected and the last two accepted
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (* x y 2)))
(assert (= y (* 2 x y)))
(assert (= y (* 2 x 3)))
(assert (= y (* 2 x)))
