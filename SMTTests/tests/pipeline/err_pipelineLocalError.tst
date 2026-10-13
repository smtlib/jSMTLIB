; OPTIONS: --pipeline
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x undeclared))
(declare-fun y () Int)
(assert (> x y))
(check-sat)
