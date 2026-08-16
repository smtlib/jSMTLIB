; bvadd is :left-assoc: (bvadd a b c) means (bvadd (bvadd a b) c), mod 2^4.
; 12 + 10 + 9 = 31 = 15 (mod 16) = #b1111.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvadd #b1100 #b1010 #b1001)))
(assert (= x #b1111))
(check-sat)
(declare-fun y () (_ BitVec 4))
(assert (= y (bvadd #b1100 #b1010 #b1001)))
(assert (= y #b0000))
(check-sat)
