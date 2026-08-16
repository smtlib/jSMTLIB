; bvand's :left-assoc sugar still requires at least two arguments -- see
; ok_bvandLeftAssocSugar.tst for the >2 case this now allows
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= (bvand x) x))
