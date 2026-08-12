; bvlshr's arguments must have the same BitVec sort
(set-logic QF_BV)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 5))
(declare-fun z () (_ BitVec 8))
(assert (= (bvlshr x y) #b111))
