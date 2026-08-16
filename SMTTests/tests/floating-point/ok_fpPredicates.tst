; fp.isNormal/isSubnormal/isZero/isInfinite/isNaN/isNegative/isPositive each take one
; FloatingPoint argument and return Bool. +zero and NaN are both easy to build exactly
; via the indexed constants, no rounding needed.
(set-logic ALL)
(declare-fun z () (_ FloatingPoint 8 24))
(declare-fun n () (_ FloatingPoint 8 24))
(assert (= z (_ +zero 8 24)))
(assert (= n (_ NaN 8 24)))
(assert (fp.isZero z))
(assert (not (fp.isNormal z)))
(assert (not (fp.isSubnormal z)))
(assert (not (fp.isInfinite z)))
(assert (not (fp.isNegative z)))
(assert (fp.isPositive z))
(assert (fp.isNaN n))
(assert (not (fp.isZero n)))
(check-sat)
