; ported from TypeCheck.checkBoolFcn
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or p q))
