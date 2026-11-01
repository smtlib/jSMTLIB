; QF_UFLIA forbids quantifiers and nonlinear arithmetic
(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
(assert (forall ((z Int)) (= z x)))
(assert (= y (* x x)))
