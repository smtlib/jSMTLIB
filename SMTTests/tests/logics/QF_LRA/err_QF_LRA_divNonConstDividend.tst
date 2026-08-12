; QF_LRA: division where the dividend is not a constant
; (covers LRA.validExpression / error path)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= y (/ x 2.0)))
