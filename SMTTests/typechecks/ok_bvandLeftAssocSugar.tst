; bvand is :left-assoc per FixedSizeBitVectors.smt2 (informal :funs-description text):
; (bvand t1 t2 t3 ...) with n > 2 args is sugar for (bvand (bvand t1 t2) t3) ...,
; so any number >= 2 of same-sort BitVec arguments should type-check.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ BitVec 4))
(declare-fun w () (_ BitVec 4))
(assert (= (bvand x y z) (bvand x (bvand y z))))
(assert (= (bvand x y z w) (bvand (bvand x y) (bvand z w))))
