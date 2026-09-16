; ported from TypeCheck.checkBadFcn
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun p () Bool)
(declare-fun q () X)
(assert (or p q))
