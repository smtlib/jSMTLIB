; AUFLIRA forbids nonlinear real multiplication and non-const-over-const division
(set-logic AUFLIRA)
(declare-const a Real)
(declare-const b Real)
; nonlinear real multiplication: a * a is not linear
(assert (= b (* a a)))
; division where dividend is not a constant (covers isLinearReal / error path)
(assert (= b (/ a 2.0)))
; array sort must be (Array Int Real) or (Array Int (Array Int Real))
(define-sort BadArr () (Array Int Int))
