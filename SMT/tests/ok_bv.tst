; checks bit vector sorts
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 1))
(declare-fun z () (_ BitVec 4))
(assert (= x #b0101 ))
(assert (= z #xa ))
