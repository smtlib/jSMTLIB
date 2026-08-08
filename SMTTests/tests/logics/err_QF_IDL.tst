; QF_IDL forbidden operations
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
; quantifier forbidden
(assert (forall ((a Int)) (>= a 0)))
; uninterpreted function forbidden
(declare-fun f (Int) Int)
; new sort forbidden
(declare-sort S 0)
; nonlinear multiplication is not IDL
(assert (>= (* x y) 0))
; rhs must be a symbol when lhs is a symbol
(assert (>= x 3))
; difference arguments must be symbols
(assert (>= (- x 1) y))
; rhs of difference comparison must be a numeral or negated numeral
(assert (>= (- x y) z))
