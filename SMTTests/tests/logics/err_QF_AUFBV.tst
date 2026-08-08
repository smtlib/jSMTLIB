; QF_AUFBV forbids quantifiers
(set-logic QF_AUFBV)
(declare-const x (_ BitVec 8))
(assert (forall ((z (_ BitVec 8))) (= z x)))
