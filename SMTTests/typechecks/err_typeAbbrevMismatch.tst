; ported from TypeCheck.checkTypeAbbrev3
(set-logic QF_UF)
(declare-sort X 1)
(declare-sort Y 0)
(define-sort Z (A) (X A))
(declare-fun q () (X Y))
(declare-fun qb () (Z Bool))
(assert (= q qb))
