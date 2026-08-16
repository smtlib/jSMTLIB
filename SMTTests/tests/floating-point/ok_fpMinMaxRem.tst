; fp.min/fp.max/fp.rem are fixed 2-arg (not chainable) -- min(1,2)=1, max(1,2)=2,
; rem(3,2)=1 (3 - 1*2).
(set-logic ALL)
(declare-fun one () (_ FloatingPoint 8 24))
(declare-fun two () (_ FloatingPoint 8 24))
(declare-fun three () (_ FloatingPoint 8 24))
(assert (= one ((_ to_fp 8 24) RNE 1.0)))
(assert (= two ((_ to_fp 8 24) RNE 2.0)))
(assert (= three ((_ to_fp 8 24) RNE 3.0)))
(assert (= one (fp.min one two)))
(assert (= two (fp.max one two)))
(assert (= one (fp.rem three two)))
(check-sat)
