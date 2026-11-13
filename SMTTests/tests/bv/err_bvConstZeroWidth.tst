; a bitvector constant's width must be at least 1, whatever its value
(set-logic QF_BV)
(assert (= #b1 (_ bv1 0)))
(assert (= #b1 (_ bv0 0)))
