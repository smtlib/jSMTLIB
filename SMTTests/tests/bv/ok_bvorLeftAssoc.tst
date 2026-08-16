; bvor is :left-assoc: (bvor a b c) means (bvor (bvor a b) c).
; #b1100 | #b1010 = #b1110; #b1110 | #b1001 = #b1111.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvor #b1100 #b1010 #b1001)))
(assert (= x #b1111))
(check-sat)
(declare-fun y () (_ BitVec 4))
(assert (= y (bvor #b1100 #b1010 #b1001)))
(assert (= y #b0000))
(check-sat)
