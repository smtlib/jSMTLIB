; (_ int_to_bv m) requires an Int argument, not BitVec
(set-logic ALL)
(declare-fun b () (_ BitVec 8))
(assert (= b ((_ int_to_bv 8) b)))
