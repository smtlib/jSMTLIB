; fp.sqrt/fp.roundToIntegral require a FloatingPoint second argument, not Int
(set-logic ALL)
(declare-fun n () Int)
(assert (= n (fp.sqrt RNE n)))
