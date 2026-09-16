; ported from TypeCheckRealsInts.checkIntRealCoercion -- exercises the Int-to-Real
; coercion paths in TypeChecker: the =/distinct argument-sort-matching loop, and the
; generic-operator symbol-table lookup fallback (an Int argument mixed with a Real
; argument in the same call)
(set-logic AUFNIRA)
(declare-fun q () Int)
(declare-fun a () Real)
(assert (= a q))
(assert (= q a))
(assert (>= a q))
(assert (>= q a))
