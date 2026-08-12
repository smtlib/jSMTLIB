; QF_NIA forbids the (jSMTLIB-specific) exponentiation operator **
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (** x 2)))
