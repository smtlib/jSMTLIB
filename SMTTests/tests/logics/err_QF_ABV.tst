; QF_ABV forbids quantifiers, UF with arguments, and new sorts
(set-logic QF_ABV)
(declare-const x (_ BitVec 8))
(assert (forall ((z (_ BitVec 8))) (= z x)))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-sort Tag 0)
