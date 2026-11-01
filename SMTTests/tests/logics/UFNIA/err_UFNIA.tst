; UFNIA forbids the ** exponentiation operator
(set-logic UFNIA)
(declare-const x Int)
(declare-const y Int)
; exponentiation is forbidden
(assert (= y (** x 2)))
