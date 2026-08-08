; AUFLIA forbids nonlinear arithmetic
(set-logic AUFLIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (* x x)))
; array sort must be (Array Int Int)
(define-sort BadArr () (Array Int Real))
