; QF_AUFLIA forbids quantifiers and nonlinear arithmetic
(set-logic QF_AUFLIA)
(declare-const x Int)
(declare-const y Int)
(assert (forall ((z Int)) (= z x)))
(assert (= y (* x x)))
; array sort must be (Array Int Int)
(define-sort BadArr () (Array Int Real))
