; fp takes exactly three arguments: sign (BitVec 1), exponent (BitVec), significand (BitVec)
(set-logic ALL)
(assert (= (_ +zero 8 24) (fp #b0 #b00000000)))
