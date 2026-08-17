; bvshl/bvlshr/bvudiv/bvurem require both arguments to have a BitVec sort -- x is Int
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () (_ BitVec 4))
(assert (= y (bvshl x y)))
