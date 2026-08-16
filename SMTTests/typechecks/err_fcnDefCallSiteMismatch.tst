; ported from TypeCheckInt.checkFcnDef1 -- call-site type mismatch through a
; define-fun result, distinct from tests/define/err_defineFunSortMismatch.tst's
; check of the definition's own body-vs-declared-result-sort mismatch
(set-logic AUFNIRA)
(declare-fun q () Int)
(declare-fun r () Int)
(define-fun f ((a Int)(b Int)) Int (+ a b))
(assert (= (f 1 2) true))
