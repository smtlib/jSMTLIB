; bvshl/bvlshr/bvudiv/bvurem require both arguments to have a BitVec sort -- y is Int
(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(declare-fun y () Int)
(assert (= x (bvlshr x y)))
