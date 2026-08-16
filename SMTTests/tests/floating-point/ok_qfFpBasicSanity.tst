; Confirms QF_FP actually enables FloatingPoint functionality (not just that the
; logic name parses): declare, build values via to_fp, and exercise fp.add/fp.leq.
; 1.0 + 2.0 = 3.0 is exact in binary32.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE 1.0)))
(assert (= y ((_ to_fp 8 24) RNE 2.0)))
(assert (= z ((_ to_fp 8 24) RNE 3.0)))
(assert (fp.leq x y z))
(assert (= z (fp.add RNE x y)))
(check-sat)
