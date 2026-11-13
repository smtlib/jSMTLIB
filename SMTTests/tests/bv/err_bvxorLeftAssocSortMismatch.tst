; bvxor's :left-assoc sugar still requires every argument to have the same BitVec sort;
; see ok_bvxorLeftAssoc.tst for the type-correct case.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun w () (_ BitVec 8))
(assert (= x (bvxor x y w)))
