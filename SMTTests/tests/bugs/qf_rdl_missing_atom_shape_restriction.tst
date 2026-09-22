; Issue #49: QF_RDL.validExpression() only called noQuantifiers() -- unlike its
; integer-difference sibling QF_IDL, it implemented no atom-shape restriction at all, so any
; Real-sorted formula (nonlinear multiplication, arbitrary comparisons) was silently accepted.
; Fixed by giving QF_RDL the same atom-shape restriction QF_IDL already has.
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(assert (>= x y))
(assert (<= x 5.0))
(assert (>= (- x y) 3.0))
(assert (>= (- x y) (- 3.0)))
(assert (>= (- x 1.0) y))
(assert (and (>= x y) (>= (- x 1.0) y)))
(assert (and (>= (- x y) 3.0) (<= (- y x) 5.0)))
(assert (>= (* x y) 0.0))
(assert (forall ((a Real)) (>= a 0.0)))
(declare-fun f (Real) Real)
(declare-sort S 0)
