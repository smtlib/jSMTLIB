; fp.rem/fp.min/fp.max require both arguments to share the same FloatingPoint sort
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 5 11))
(assert (= x (fp.rem x y)))
