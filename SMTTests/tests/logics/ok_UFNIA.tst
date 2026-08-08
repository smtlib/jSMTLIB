; UFNIA: quantifiers and UF allowed, no ** exponentiation
(set-logic UFNIA)
(declare-sort MySort 0)
(declare-const x Int)
(declare-const y Int)
; nonlinear integer multiplication is allowed
(assert (= y (* x x)))
; UF declaration is allowed
(declare-fun f (Int) Int)
(assert (= y (f x)))
; quantified expressions are allowed
(assert (forall ((z Int)) (>= (* z z) 0)))
(assert (exists ((z Int)) (= (* z z) x)))
