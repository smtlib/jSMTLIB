; (_ rotate_left n)/(_ rotate_right n) take exactly one BitVec argument
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (= #b0100 ((_ rotate_left 1) x y)))
