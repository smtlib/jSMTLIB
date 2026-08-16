; -> in its base, non-sugared 2-argument form -- see err_arrowArity0.tst/
; err_arrowArity1.tst for too-few-argument errors and
; ok_arrowRightAssocSugar.tst for the (currently broken) 3-arg sugar
(set-logic ALL)
(declare-fun f () (-> Int Bool))
