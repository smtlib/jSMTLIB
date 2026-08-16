; bvand's :left-assoc sugar still requires every argument to share the same BitVec
; sort -- here w has a different width than x and y -- see ok_bvandLeftAssoc.tst for
; the type-correct 3-arg case.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun w () (_ BitVec 8))
(assert (= x (bvand x y w)))
