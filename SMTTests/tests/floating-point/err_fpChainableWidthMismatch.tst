; fp.leq/fp.lt/fp.geq/fp.gt/fp.eq require every argument to share the same FloatingPoint
; sort -- y has a different width than x, distinct from the "not FloatingPoint at all"
; case covered by err_fpLeqSortMismatch.tst.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 5 11))
(assert (fp.leq x y))
