; (_ fp.to_ubv m)/(_ fp.to_sbv m) require a FloatingPoint second argument, not Int
(set-logic ALL)
(declare-fun n () Int)
(assert (= #b0000 ((_ fp.to_ubv 4) RNE n)))
