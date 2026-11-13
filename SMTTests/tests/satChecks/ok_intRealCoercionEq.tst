; = with an Int and a Real under AUFNIRA. Core declares = polymorphically, (par (A) (= A A Bool)),
; so whether AUFNIRA's Int-to-Real sugar for (op Real Real s) applies to it is undecided (#163 item 30).
(set-logic AUFNIRA)
(declare-fun q () Int)
(declare-fun a () Real)
(assert (= a q))
(assert (= q a))
