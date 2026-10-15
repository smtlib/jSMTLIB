; OPTIONS: --pipeline --abort
(set-logic QF_LIA)
(declare-fun x () Int)
(push 1)
(pop 2)
(declare-fun y () Int)
(assert (> x y))
(check-sat)
