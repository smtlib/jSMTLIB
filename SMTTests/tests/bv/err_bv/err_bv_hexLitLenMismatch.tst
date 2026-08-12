; A hex bitvector literal's length must match the declared sort
(set-logic QF_BV)
(declare-fun z () (_ BitVec 4))
(assert (= z #xab ))
