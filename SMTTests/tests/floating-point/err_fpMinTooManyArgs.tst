; fp.min is fixed 2-arg -- unlike fp.leq & co., it is not declared :chainable/:left-assoc,
; so more than 2 arguments must still be rejected.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (= x (fp.min x y z)))
