; (_ to_fp_unsigned eb sb) requires a BitVec second argument, not Int
(set-logic ALL)
(declare-fun n () Int)
(assert (= ((_ to_fp_unsigned 8 24) RNE n) (_ +zero 8 24)))
