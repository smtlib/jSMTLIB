; fp.to_real converts a FloatingPoint value to Real. 2.0 is exact in binary32.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE 2.0)))
(assert (= (fp.to_real x) 2.0))
(check-sat)
