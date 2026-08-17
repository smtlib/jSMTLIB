; fp.fma requires a RoundingMode first argument, not Bool
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun b () Bool)
(assert (= x (fp.fma b x x x)))
