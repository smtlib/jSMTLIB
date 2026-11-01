; AUFLIRA: a product of any arity is linear only if at most one factor is not a coefficient;
; the first assertion is rejected, the second accepted
(set-logic AUFLIRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= y (* x y 2.0)))
(assert (= y (* 2.0 x 3.0)))
