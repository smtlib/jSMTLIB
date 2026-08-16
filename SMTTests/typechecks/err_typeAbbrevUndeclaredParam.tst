; ported from TypeCheck.checkTypeAbbrev2 -- Z's own parameter A is not in scope
; outside Z's definition
(set-logic QF_UF)
(declare-sort X 1)
(declare-sort Y 0)
(define-sort Z (A) (X A))
(declare-fun q () (X Y))
(declare-fun qb () (Z A))
