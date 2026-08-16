; fp.lt's :chainable sugar still requires every argument to have sort FloatingPoint -- b is Bool.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun b () Bool)
(assert (fp.lt x y b))
