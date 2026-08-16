; exists is likewise forbidden in QF_UF (forall's version of this is covered by
; tests/logics/err_QF_UF.tst); ported from TypeCheck.checkExists
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun p () Bool)
(declare-fun q () X)
(assert (exists ((r Bool)(s X)) (and r p)))
