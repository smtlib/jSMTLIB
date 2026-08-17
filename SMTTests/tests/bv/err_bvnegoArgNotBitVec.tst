; bvnego requires a BitVec argument, not Int
(set-logic ALL)
(declare-fun x () Int)
(assert (bvnego x))
