; QF_RDL: quantifier-free real difference logic; no UF, no new sorts
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(assert (>= (- x y) 1.0))
(assert (<= x 5.0))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyReal () Real)
