; (_ repeat n) requires n != 0
(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(assert (= x ((_ repeat 0) x)))
