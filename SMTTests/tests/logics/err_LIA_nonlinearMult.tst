; LIA forbids nonlinear arithmetic: x * x is not linear
(set-logic LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (* x x)))
