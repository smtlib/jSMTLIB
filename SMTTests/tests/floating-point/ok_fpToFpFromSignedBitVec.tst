; (_ to_fp eb sb) overload (d): RoundingMode + BitVec -- convert from a signed
; 2's-complement integer. #b0011 (4-bit) is 3.
(set-logic ALL)
(declare-fun b () (_ BitVec 4))
(assert (= b #b0011))
(assert (= ((_ to_fp 8 24) RNE b) ((_ to_fp 8 24) RNE 3.0)))
(check-sat)
