; AUFNIRA's :extensions widen an Int term to Real only in (op t1 t) / (op t t1) with t1 Int,
; t Real and op of rank (op Real Real s), and in (/ t1 t2) with t1, t2 Int.
; Each assertion below is outside those forms, so each is a sort error.
(set-logic AUFNIRA)
(declare-const i Int)
(declare-const r Real)
(declare-const b Bool)
(declare-fun h (Real) Bool)
(declare-fun g (Real Real) Bool)
(declare-fun k (Real Real Real) Bool)
; unary rank
(assert (h i))
(assert (is_int i))
; rank (g Real Real Bool), but no Real argument
(assert (g i i))
; ternary rank
(assert (k i r r))
; ite's rank (ite Bool A A A) is not of the form (op Real Real s)
(assert (= r (ite b i r)))
