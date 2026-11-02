; QF_AX forbids quantifiers and UF with arguments
(set-logic QF_AX)
(declare-sort A 0)
(declare-const x A)
(assert (forall ((z A)) (= z x)))
(declare-fun f (A) A)
