; QF_UFIDL: quantifier-free integer difference logic with UF
(set-logic QF_UFIDL)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (>= (- x y) 1))
(assert (= x (f y)))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyInt () Int)
