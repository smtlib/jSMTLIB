; (_ extract i j) requires a BitVec argument, not Int
(set-logic ALL)
(declare-fun x () Int)
(assert (= #b0100 ((_ extract 3 0) x)))
