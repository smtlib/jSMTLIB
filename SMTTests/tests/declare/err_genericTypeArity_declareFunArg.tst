; ported from TypeCheck.checkGenericType3 -- a user-declared parameterized sort (X,
; arity 1) referenced later with the wrong number of type arguments (0, as a bare
; declare-fun argument sort). Confirmed via earlier investigation that no other .tst
; test covers this: tests/declare/err_declareSort*.tst only test malformed
; declare-sort syntax and re-declaration, and tests/array/array2/err_array2_arity*.tst
; only cover the built-in Array sort's arity, not a user-declared one.
(set-logic QF_UF)
(declare-sort X 1)
(declare-sort Y 0)
(declare-fun p () Bool)
(declare-fun q () (X Y))
(declare-fun qb () (X Bool))
(declare-fun r () Y)
(declare-fun f (Y X) Bool)
