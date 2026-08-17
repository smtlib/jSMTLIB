; fp.add/fp.sub/fp.mul/fp.div take exactly three arguments: RoundingMode + two FloatingPoint
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (fp.add RNE x)))
