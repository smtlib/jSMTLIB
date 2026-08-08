; QF_NRA forbids quantifiers, uninterpreted functions, and new sorts
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
; quantifier is forbidden
(assert (forall ((z Real)) (>= z 0.0)))
; uninterpreted function is forbidden
(declare-fun f (Real) Real)
; new sort is forbidden
(declare-sort S 0)
