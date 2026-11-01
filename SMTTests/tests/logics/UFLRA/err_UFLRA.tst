; UFLRA forbids nonlinear real multiplication
(set-logic UFLRA)
(declare-const a Real)
(declare-const b Real)
; nonlinear multiplication: a * a is not linear
(assert (= b (* a a)))
