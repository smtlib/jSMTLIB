; (_ to_fp_unsigned eb sb): RoundingMode + BitVec -- convert from an unsigned integer.
; #b0011 (4-bit, unsigned) is 3.
(set-logic ALL)
(declare-fun b () (_ BitVec 4))
(assert (= b #b0011))
(assert (= ((_ to_fp_unsigned 8 24) RNE b) ((_ to_fp 8 24) RNE 3.0)))
(check-sat)
