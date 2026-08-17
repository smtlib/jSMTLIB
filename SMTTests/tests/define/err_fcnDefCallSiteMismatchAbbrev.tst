; ported from TypeCheckInt.checkFcnDef2 -- same as err_fcnDefCallSiteMismatch.tst,
; but one of the define-fun's parameter sorts is given via a sort abbreviation
(set-logic AUFNIRA)
(define-sort Z () Int)
(declare-fun q () Int)
(declare-fun r () Int)
(define-fun f ((a Int)(b Z)) Int (+ a b))
(assert (= (f 1 2) true))
