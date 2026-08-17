; (_ zero_extend n)/(_ sign_extend n) take exactly one numeral index
(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(assert (= #b0011 ((_ zero_extend 2 3) x)))
