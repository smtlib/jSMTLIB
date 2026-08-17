; bvand's :left-assoc sugar requires every argument to share the same BitVec sort,
; not just the first two -- see ok_bvandLeftAssocSugar.tst for the matching-sorts case
; and tests/bv/err_bv2/err_bv2_bvandArgSortMismatch.tst for the 2-arg mismatch case
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ BitVec 8))
(assert (= (bvand x y z) x))
