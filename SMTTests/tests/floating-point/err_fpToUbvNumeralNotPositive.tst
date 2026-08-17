; (_ fp.to_ubv m)/(_ fp.to_sbv m) require m > 0
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun b () (_ BitVec 4))
(assert (= b ((_ fp.to_ubv 0) RNE x)))
