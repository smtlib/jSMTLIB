; QF_BV forbids quantifiers
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (forall ((z (_ BitVec 8))) (= z x)))
