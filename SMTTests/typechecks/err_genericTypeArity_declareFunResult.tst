; ported from TypeCheck.checkGenericType6 -- same arity error as
; err_genericTypeArity_declareFunArg.tst, but the bad reference is in a
; declare-fun's *result* sort position rather than an argument position
(set-logic QF_UF)
(declare-sort X 1)
(declare-sort Y 0)
(declare-fun p () Bool)
(declare-fun q () (X Y))
(declare-fun qb () (X Bool))
(declare-fun r () Y)
(declare-fun f () X)
