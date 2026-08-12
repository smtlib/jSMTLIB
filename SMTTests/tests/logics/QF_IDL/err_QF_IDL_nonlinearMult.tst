; QF_IDL: lhs must be a symbol or a difference, not a nonlinear multiplication
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (>= (* x y) 0))
