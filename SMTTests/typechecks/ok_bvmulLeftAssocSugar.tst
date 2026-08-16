; bvmul is :left-assoc -- see ok_bvandLeftAssocSugar.tst
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ BitVec 4))
(assert (= (bvmul x y z) (bvmul (bvmul x y) z)))
