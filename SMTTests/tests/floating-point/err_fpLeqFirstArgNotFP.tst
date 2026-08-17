; fp.leq/fp.lt/fp.geq/fp.gt/fp.eq require every argument to be FloatingPoint -- x is Int
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.leq x y))
