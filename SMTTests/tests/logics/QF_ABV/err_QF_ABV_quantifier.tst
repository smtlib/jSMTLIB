; QF_ABV forbids quantifiers
(set-logic QF_ABV)
(declare-const x (_ BitVec 8))
(assert (forall ((z (_ BitVec 8))) (= z x)))
