; (_ rotate_left n)/(_ rotate_right n) require a BitVec argument, not Int
(set-logic ALL)
(declare-fun x () Int)
(assert (= #b0100 ((_ rotate_left 1) x)))
