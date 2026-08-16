; bvand is :left-assoc: (bvand a b c) means (bvand (bvand a b) c).
; #b1100 & #b1010 = #b1000; #b1000 & #b1001 = #b1000.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvand #b1100 #b1010 #b1001)))
(assert (= x #b1000))
(check-sat)
(declare-fun y () (_ BitVec 4))
(assert (= y (bvand #b1100 #b1010 #b1001)))
(assert (= y #b0111))
(check-sat)
