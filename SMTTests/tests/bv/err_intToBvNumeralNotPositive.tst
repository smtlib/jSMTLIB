; (_ int_to_bv m) requires m > 0
(set-logic ALL)
(declare-fun x () Int)
(assert (= #b0 ((_ int_to_bv 0) x)))
