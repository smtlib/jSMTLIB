; A binary bitvector literal's length must match the declared sort
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #b010 ))
