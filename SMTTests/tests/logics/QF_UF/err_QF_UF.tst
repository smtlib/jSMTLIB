; QF_UF forbids quantifiers
(set-logic QF_UF)
(declare-sort A 0)
(declare-const x A)
(assert (forall ((z A)) (= z x)))
