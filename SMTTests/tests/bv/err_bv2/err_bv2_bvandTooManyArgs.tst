; bvand is :left-assoc, so 3 arguments is fine by itself, but all arguments must
; share the same BitVec sort -- here they don't (3 vs 5 vs 8 bits)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 5))
(declare-fun z () (_ BitVec 8))
(assert (= (bvand x y z) #b111))
