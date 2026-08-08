; QF_UFBV forbids quantifiers
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 8))
; quantifier is forbidden
(assert (forall ((z (_ BitVec 8))) (= z x)))
