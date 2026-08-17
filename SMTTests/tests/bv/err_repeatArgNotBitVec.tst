; (_ repeat n) requires a BitVec argument, not Int
(set-logic ALL)
(declare-fun x () Int)
(assert (= #b1010 ((_ repeat 2) x)))
