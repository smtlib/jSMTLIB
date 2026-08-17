; bvnego is a one-argument overflow-check predicate
(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (bvnego x y))
