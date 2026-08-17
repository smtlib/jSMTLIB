; (_ fp.to_ubv m)/(_ fp.to_sbv m) take exactly one numeral index
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= #b0000 ((_ fp.to_ubv 4 5) RNE x)))
