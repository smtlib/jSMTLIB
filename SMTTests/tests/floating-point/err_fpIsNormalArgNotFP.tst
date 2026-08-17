; fp.isNormal/isSubnormal/isZero/isInfinite/isNaN/isNegative/isPositive require a
; FloatingPoint argument, not Int
(set-logic ALL)
(declare-fun n () Int)
(assert (fp.isNormal n))
