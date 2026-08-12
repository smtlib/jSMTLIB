; QF_LIA forbids nonlinear arithmetic: x * x is not linear
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= y (* x x)))
