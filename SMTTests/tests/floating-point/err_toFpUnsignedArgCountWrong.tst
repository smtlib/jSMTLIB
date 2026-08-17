; (_ to_fp_unsigned eb sb) takes exactly two arguments: RoundingMode, BitVec
(set-logic ALL)
(declare-fun b () (_ BitVec 4))
(assert (= ((_ to_fp_unsigned 8 24) RNE b b) (_ +zero 8 24)))
