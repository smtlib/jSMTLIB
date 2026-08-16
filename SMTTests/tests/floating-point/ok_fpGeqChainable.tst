; fp.geq is :chainable. 3.0 >= 2.0 >= 1.0 is true; 3.0 >= 1.0 >= 2.0 is false
; (1.0 >= 2.0 fails).
(set-logic ALL)
(declare-fun one () (_ FloatingPoint 8 24))
(declare-fun two () (_ FloatingPoint 8 24))
(declare-fun three () (_ FloatingPoint 8 24))
(assert (= one ((_ to_fp 8 24) RNE 1.0)))
(assert (= two ((_ to_fp 8 24) RNE 2.0)))
(assert (= three ((_ to_fp 8 24) RNE 3.0)))
(assert (fp.geq three two one))
(check-sat)
(assert (fp.geq three one two))
(check-sat)
