; QF_IDL: rhs of a difference comparison must be a numeral or negated numeral
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (>= (- x y) z))
