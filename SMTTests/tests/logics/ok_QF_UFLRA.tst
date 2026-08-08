; QF_UFLRA: quantifier-free linear real arithmetic with UF and new sorts allowed
(set-logic QF_UFLRA)
(declare-sort MySort 0)
(declare-const a Real)
(declare-const b Real)
; uninterpreted function is allowed
(declare-fun f (Real) Real)
; linear real expressions
(assert (= b (+ a 1.0)))
(assert (= b (- a 1.0)))
(assert (= b (* 2.0 a)))
(assert (= b (* a 2.0)))
(assert (>= a 0.0))
; UF application
(assert (= b (f a)))
