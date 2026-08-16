; Confirms QF_FP's bundling of FixedSizeBitVectors (not FloatingPoint alone) is
; actually necessary: the fp constructor takes three BitVec arguments, and
; fp.to_ubv converts an FP value back to a BitVec. +0's bit pattern is all zeros;
; 3.0 -> #b0011 (4-bit unsigned).
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (= x (_ +zero 8 24)))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= y ((_ to_fp 8 24) RNE 3.0)))
(assert (= ((_ fp.to_ubv 4) RNE y) #b0011))
(check-sat)
