; AUFLIA: quantifiers + UF + linear integer arithmetic + arrays
(set-logic AUFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= y (+ x 1)))
(assert (= y (* 3 x)))
(assert (forall ((z Int)) (>= (f z) 0)))
(define-sort MyArr () (Array Int Int))
