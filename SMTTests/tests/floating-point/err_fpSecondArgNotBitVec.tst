; fp's second (exponent) argument must have a BitVec sort, not Int
(set-logic ALL)
(declare-fun e () Int)
(assert (= (_ +zero 8 24) (fp #b0 e #b00000000000000000000000)))
