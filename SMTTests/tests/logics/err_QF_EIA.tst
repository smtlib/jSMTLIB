; QF_EIA forbids quantifiers, uninterpreted functions, and new sorts
(set-logic QF_EIA)
(declare-const x Int)
(declare-const y Int)
(assert (forall ((z Int)) (>= z 0)))
(declare-fun f (Int) Int)
(declare-sort S 0)
