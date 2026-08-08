; QF_AUFLIA: quantifier-free linear integer arithmetic + arrays + UF
(set-logic QF_AUFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= y (+ x 1)))
(assert (= y (* 3 x)))
(assert (= y (f x)))
(define-sort MyArr () (Array Int Int))
