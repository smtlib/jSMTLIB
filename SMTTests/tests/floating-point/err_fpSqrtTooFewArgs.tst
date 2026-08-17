; fp.sqrt/fp.roundToIntegral take exactly two arguments: RoundingMode, FloatingPoint
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (fp.sqrt RNE)))
