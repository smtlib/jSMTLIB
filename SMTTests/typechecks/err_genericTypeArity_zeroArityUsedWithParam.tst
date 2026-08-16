; ported from TypeCheck.checkGenericType5 -- a user-declared 0-arity sort (Y) used
; as though it were parameterized
(set-logic QF_UF)
(declare-sort X 1)
(declare-sort Y 0)
(declare-fun p () Bool)
(declare-fun q () (X Y))
(declare-fun qb () (X Bool))
(declare-fun r () Y)
(declare-fun f ((Y Y)) Bool)
