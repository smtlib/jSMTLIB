; QF_LRA forbids nonlinear arithmetic: x * x is not linear
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* x x)))
