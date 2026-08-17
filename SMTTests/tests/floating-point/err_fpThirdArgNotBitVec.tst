; fp's third (significand) argument must have a BitVec sort, not Int
(set-logic ALL)
(declare-fun sig () Int)
(assert (= (_ +zero 8 24) (fp #b0 #b00000000 sig)))
