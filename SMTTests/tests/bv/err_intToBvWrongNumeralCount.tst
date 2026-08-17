; (_ int_to_bv m) takes exactly one numeral index
(set-logic ALL)
(declare-fun x () Int)
(assert (= #b00000000 ((_ int_to_bv 8 3) x)))
