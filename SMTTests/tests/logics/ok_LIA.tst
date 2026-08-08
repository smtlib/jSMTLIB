; LIA allows quantifiers and linear integer arithmetic, no UF, no new sorts
(set-logic LIA)
(declare-const x Int)
(declare-const y Int)
; linear expressions
(assert (= y (+ x 1)))
(assert (= y (- x 1)))
(assert (= y (* 3 x)))
(assert (= y (* x 3)))
(assert (>= x 0))
; quantified expressions are allowed in LIA
(assert (forall ((z Int)) (>= z 0)))
(assert (exists ((z Int)) (= z x)))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyInt () Int)
