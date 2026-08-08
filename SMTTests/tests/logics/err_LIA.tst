; LIA forbids nonlinear expressions, uninterpreted functions, and new sorts
(set-logic LIA)
(declare-const x Int)
(declare-const y Int)
; nonlinear multiplication: x * x is not linear
(assert (= y (* x x)))
; uninterpreted function declaration is not allowed
(declare-fun f (Int) Int)
; new sort declaration is not allowed
(declare-sort S 0)
