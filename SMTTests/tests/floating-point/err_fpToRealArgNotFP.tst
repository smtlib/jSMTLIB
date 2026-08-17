; fp.to_real requires a FloatingPoint argument, not Int
(set-logic ALL)
(declare-fun n () Int)
(assert (= 0.0 (fp.to_real n)))
