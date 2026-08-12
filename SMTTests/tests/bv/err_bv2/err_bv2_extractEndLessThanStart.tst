; extract's end index must not be less than the start index
(set-logic QF_BV)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 5))
(declare-fun z () (_ BitVec 8))
(assert (= ((_ extract 1 2) z) x))
