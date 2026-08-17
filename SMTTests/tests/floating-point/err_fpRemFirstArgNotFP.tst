; fp.rem/fp.min/fp.max require the first argument to be FloatingPoint, not Int
(set-logic ALL)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun n () Int)
(assert (= y (fp.rem n y)))
