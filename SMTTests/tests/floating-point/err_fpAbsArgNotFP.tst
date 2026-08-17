; fp.abs/fp.neg require a FloatingPoint argument, not Int
(set-logic ALL)
(declare-fun n () Int)
(assert (fp.isNaN (fp.abs n)))
