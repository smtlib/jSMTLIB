; @'s second argument must match the arrow sort's domain -- see ok_hoApplyBasic.tst
; for why ALL is the only logic this is reachable under
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(declare-fun y () Bool)
(assert (@ f y))
