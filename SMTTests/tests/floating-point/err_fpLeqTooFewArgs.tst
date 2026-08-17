; fp.leq/fp.lt/fp.geq/fp.gt/fp.eq are :chainable, requiring at least two arguments
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.leq x))
