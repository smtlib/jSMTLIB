; fp.add/fp.sub/fp.mul/fp.div require a RoundingMode first argument, not Bool
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun b () Bool)
(assert (= x (fp.add b x y)))
