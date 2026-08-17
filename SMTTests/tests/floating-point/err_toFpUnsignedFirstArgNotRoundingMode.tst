; (_ to_fp_unsigned eb sb) requires a RoundingMode first argument, not Bool
(set-logic ALL)
(declare-fun b () (_ BitVec 4))
(declare-fun bl () Bool)
(assert (= ((_ to_fp_unsigned 8 24) bl b) (_ +zero 8 24)))
