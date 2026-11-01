; QF_UF: quantifier-free with uninterpreted sorts and functions
(set-logic QF_UF)
(declare-sort A 0)
(declare-const x A)
(declare-fun f (A) A)
(assert (= x (f x)))
