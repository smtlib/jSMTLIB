; fp.eq is :chainable (IEEE 754 equality, distinct from =). 1.0 = 1.0 = 1.0 is true;
; 1.0 = 1.0 = 2.0 is false.
(set-logic ALL)
(declare-fun one () (_ FloatingPoint 8 24))
(declare-fun two () (_ FloatingPoint 8 24))
(assert (= one ((_ to_fp 8 24) RNE 1.0)))
(assert (= two ((_ to_fp 8 24) RNE 2.0)))
(assert (fp.eq one one one))
(check-sat)
(assert (fp.eq one one two))
(check-sat)
