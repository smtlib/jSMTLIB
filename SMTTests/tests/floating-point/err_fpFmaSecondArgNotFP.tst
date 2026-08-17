; fp.fma requires the second argument to be FloatingPoint, not Int
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun n () Int)
(assert (= x (fp.fma RNE n x x)))
