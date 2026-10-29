; A quantifier as a function argument (a Bool term). Simplify's adapter does not translate one
; and reports an error.
(set-logic AUFLIA)
(declare-fun g (Bool) Int)
(push 1)
(assert (not (= (g (forall ((y Int)) (> y 0))) (g false))))
(check-sat)
(pop 1)
(assert (not (= (g (exists ((y Int)) (> y 0))) (g true))))
(check-sat)
