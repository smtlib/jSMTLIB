; ported from TypeCheckInt.checkFcnDef
(set-logic AUFNIRA)
(declare-fun q () Int)
(declare-fun r () Int)
(define-fun f ((a Int)(b Int)) Int (+ a b))
(assert (= (f 1 2) 3))
