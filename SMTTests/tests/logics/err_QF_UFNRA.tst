; QF_UFNRA forbids quantifiers
(set-logic QF_UFNRA)
(declare-const a Real)
(declare-const b Real)
; quantifier is forbidden
(assert (forall ((z Real)) (>= z 0.0)))
