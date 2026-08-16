; bvadd's :left-assoc sugar still requires every argument to share the same BitVec
; sort -- see err_bvandLeftAssocSortMismatch.tst
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun w () (_ BitVec 8))
(assert (= x (bvadd x y w)))
