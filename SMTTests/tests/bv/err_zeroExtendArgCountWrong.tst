; (_ zero_extend n)/(_ sign_extend n) take exactly one BitVec argument
(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(assert (= #b0011 ((_ zero_extend 2) x y)))
