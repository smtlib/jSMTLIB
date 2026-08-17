; fp.fma takes exactly four arguments: RoundingMode + three FloatingPoint
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (fp.fma RNE x x)))
