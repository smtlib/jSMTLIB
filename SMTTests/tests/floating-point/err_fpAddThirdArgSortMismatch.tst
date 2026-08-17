; fp.add/fp.sub/fp.mul/fp.div require both FloatingPoint arguments to share the same sort
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 5 11))
(assert (= x (fp.add RNE x y)))
