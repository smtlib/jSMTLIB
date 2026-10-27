; #160: a term ite with a comparison as its condition
(set-logic QF_LIA)
(declare-fun x () Int)
(push 1)
(assert (= (ite (< x 0) (- x) x) (- 1)))
(check-sat)
(pop 1)
(assert (= (ite (< x 0) (- x) x) 3))
(check-sat)
