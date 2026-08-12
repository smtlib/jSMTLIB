; Two bit-vector-sorted variables of different lengths cannot be compared
(set-logic QF_BV)
(declare-fun y () (_ BitVec 1))
(declare-fun z () (_ BitVec 4))
(assert (= z y ))
