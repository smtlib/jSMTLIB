; @ in its base, non-sugared 2-argument form -- see err_atArity0.tst/err_atArity1.tst
; for too-few-argument errors and ok_atLeftAssocSugar.tst for the (currently
; broken) 3-arg sugar. err_atNotArrowSort.tst/err_atDomainMismatch.tst cover sort
; errors at this same arity.
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(declare-fun x () Int)
(assert (@ f x))
