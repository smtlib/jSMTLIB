; ported from TypeCheck.checkLet
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun p () Bool)
(declare-fun q () X)
(assert (let ((r true)(s q)) (not r)))
