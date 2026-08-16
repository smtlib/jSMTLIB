; fp constructs a FloatingPoint value from a 1-bit sign, an eb-bit exponent, and an
; (sb-1)-bit significand (the hidden bit is not represented). +0 has all bits 0.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (= x (_ +zero 8 24)))
(check-sat)
