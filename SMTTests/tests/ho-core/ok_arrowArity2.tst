; -> in its base, non-sugared 2-argument form -- see err_arrowArity0.tst/
; err_arrowArity1.tst for too-few-argument errors and
; ok_atLeftAssocSugarCombined.tst for the 3-arg :right-assoc sugar case.
(set-logic ALL)
(declare-fun f () (-> Int Bool))
