; AUFNIRA's :extensions make (op t1 t), with t1 an Int and op declared (op Real Real s), sugar
; for (op (to_real t1) t); likewise (op t t1). So >= takes an Int mixed with a Real.
; (= is in ok_intRealCoercionEq.tst: whether that sugar covers the polymorphic = is undecided.)
(set-logic AUFNIRA)
(declare-fun q () Int)
(declare-fun a () Real)
(assert (>= a q))
(assert (>= q a))
