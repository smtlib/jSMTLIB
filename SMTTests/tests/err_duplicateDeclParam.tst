; duplicate declaration in forall
(set-logic QF_LIA)
(assert (forall ((x Int)(x Int)) (= x 0)))
