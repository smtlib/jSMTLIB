; (_ zero_extend n)/(_ sign_extend n) require a BitVec argument, not Int
(set-logic ALL)
(declare-fun x () Int)
(assert (= #b0011 ((_ zero_extend 2) x)))
