; QF_NIA: quantifier-free nonlinear integer arithmetic, no UF
; Nonlinear multiplication is allowed
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
; nonlinear multiplication is allowed in QF_NIA
(assert (= y (* x x)))
(assert (= y (* x y)))
(assert (>= (* x x) 0))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyInt () Int)
