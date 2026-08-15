; ubv_to_int/sbv_to_int require a BitVec argument, not Int
(set-logic ALL)
(declare-fun x () Int)
(assert (= x (ubv_to_int x)))
