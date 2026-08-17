; (_ repeat n) takes exactly one BitVec argument
(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(assert (= #b1010 ((_ repeat 2) x y)))
