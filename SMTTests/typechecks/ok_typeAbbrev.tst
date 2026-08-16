; ported from TypeCheck.checkTypeAbbrev
(set-logic QF_UF)
(declare-sort X 1)
(declare-sort Y 0)
(define-sort Z () (X Y))
(declare-fun q () (X Y))
(declare-fun qb () Z)
(assert (= q qb))
