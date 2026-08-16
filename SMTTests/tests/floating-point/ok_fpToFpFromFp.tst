; (_ to_fp eb sb) overload (b): RoundingMode + FloatingPoint -- convert between
; precisions (source (mb,nb) need not match the target (eb,sb)). 3.0 is exact in
; both binary32 and binary64.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 11 53))
(assert (= x ((_ to_fp 8 24) RNE 3.0)))
(assert (= y ((_ to_fp 11 53) RNE 3.0)))
(assert (= y ((_ to_fp 11 53) RNE x)))
(check-sat)
