; QF_UFLRA forbids quantifiers and nonlinear real multiplication
(set-logic QF_UFLRA)
(declare-const a Real)
(declare-const b Real)
; quantifier is forbidden
(assert (forall ((z Real)) (>= z 0.0)))
; nonlinear multiplication: a * a is not linear
(assert (= b (* a a)))
