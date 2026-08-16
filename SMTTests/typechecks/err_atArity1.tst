; @ with only one argument -- see err_atArity0.tst
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(assert (@ f))
