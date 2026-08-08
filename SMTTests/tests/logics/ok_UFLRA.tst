; UFLRA: linear real arithmetic with UF, new sorts, and quantifiers allowed
(set-logic UFLRA)
(declare-sort MySort 0)
(declare-const a Real)
(declare-const b Real)
; linear real expressions
(assert (= b (+ a 1.0)))
(assert (= b (- a 1.0)))
(assert (= b (* 2.0 a)))
; UF declaration is allowed
(declare-fun f (Real) Real)
(assert (= b (f a)))
; quantified expressions are allowed in UFLRA
(assert (forall ((z Real)) (>= z 0.0)))
(assert (exists ((z Real)) (= z a)))
