; QF_UFNRA: quantifier-free nonlinear real arithmetic with UF and new sorts
(set-logic QF_UFNRA)
(declare-sort MySort 0)
(declare-const a Real)
(declare-const b Real)
; nonlinear multiplication is allowed
(assert (= b (* a a)))
; UF declaration is allowed
(declare-fun f (Real) Real)
(assert (= b (f a)))
; new sort constant
(declare-const s MySort)
