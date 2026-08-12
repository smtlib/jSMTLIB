; QF_LRA forbids quantifiers
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (forall ((z Real)) (>= z 0.0)))
