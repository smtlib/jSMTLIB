; = with an Int and a Real under AUFNIRA. Core declares = polymorphically, (par (A) (= A A Bool)); jSMTLIB
; reads the Int as to_real, taking the :extensions sugar to cover = (#211 item 1).
(set-logic AUFNIRA)
(declare-fun q () Int)
(declare-fun a () Real)
(assert (= a q))
(assert (= q a))
