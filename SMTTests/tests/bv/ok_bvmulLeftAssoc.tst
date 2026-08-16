; bvmul is :left-assoc: (bvmul a b c) means (bvmul (bvmul a b) c), mod 2^4.
; 12 * 10 = 120 = 8 (mod 16); 8 * 9 = 72 = 8 (mod 16). So the result is #b1000.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvmul #b1100 #b1010 #b1001)))
(assert (= x #b1000))
(check-sat)
(declare-fun y () (_ BitVec 4))
(assert (= y (bvmul #b1100 #b1010 #b1001)))
(assert (= y #b0001))
(check-sat)
