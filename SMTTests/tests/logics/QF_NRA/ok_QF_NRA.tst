; QF_NRA: quantifier-free nonlinear real arithmetic, no UF, no new sorts
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
; nonlinear multiplication is allowed in QF_NRA
(assert (= b (* a a)))
(assert (>= (* a b) 0.0))
(assert (= b (+ (* a a) 1.0)))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyReal () Real)
