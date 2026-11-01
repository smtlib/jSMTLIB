; QF_UFIDL forbids quantifiers
(set-logic QF_UFIDL)
(declare-const x Int)
(assert (forall ((z Int)) (= z x)))
