; QF_NIA forbids exponentiation (**), UF, and new sorts
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (** x 2)))
; uninterpreted function is forbidden
(declare-fun f (Int) Int)
; new sort is forbidden
(declare-sort S 0)
