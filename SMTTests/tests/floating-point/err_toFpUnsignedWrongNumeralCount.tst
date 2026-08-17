; (_ to_fp_unsigned eb sb) takes exactly two numeral indices
(set-logic ALL)
(declare-fun b () (_ BitVec 4))
(assert (= ((_ to_fp_unsigned 8) RNE b) (_ +zero 8 24)))
