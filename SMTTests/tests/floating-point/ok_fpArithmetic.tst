; fp.add/fp.sub/fp.mul/fp.div take a RoundingMode plus two same-sort FloatingPoint
; arguments; fp.sqrt/fp.roundToIntegral take a RoundingMode plus one. 1.0 + 2.0 = 3.0
; is exact in binary32, so no solver needs any rounding subtlety to verify it.
(set-logic ALL)
(declare-fun one () (_ FloatingPoint 8 24))
(declare-fun two () (_ FloatingPoint 8 24))
(declare-fun three () (_ FloatingPoint 8 24))
(assert (= one ((_ to_fp 8 24) RNE 1.0)))
(assert (= two ((_ to_fp 8 24) RNE 2.0)))
(assert (= three ((_ to_fp 8 24) RNE 3.0)))
(assert (= three (fp.add RNE one two)))
(assert (= one (fp.sub RNE three two)))
(assert (= two (fp.mul RNE one two)))
(assert (= one (fp.div RNE two two)))
(assert (= two (fp.sqrt RNE (fp.mul RNE two two))))
(assert (= three (fp.roundToIntegral RNE three)))
(assert (= three (fp.fma RNE one two one)))
(check-sat)
