; (_ fp.to_ubv m)/(_ fp.to_sbv m) require a RoundingMode first argument, not Bool
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun b () Bool)
(assert (= #b0000 ((_ fp.to_ubv 4) b x)))
