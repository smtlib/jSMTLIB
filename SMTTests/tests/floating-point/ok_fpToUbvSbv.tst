; (_ fp.to_ubv m)/(_ fp.to_sbv m) convert a FloatingPoint value (given a RoundingMode)
; to an m-bit BitVec. 3.0 -> #b0011 (4-bit).
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE 3.0)))
(assert (= ((_ fp.to_ubv 4) RNE x) #b0011))
(assert (= ((_ fp.to_sbv 4) RNE x) #b0011))
(check-sat)
