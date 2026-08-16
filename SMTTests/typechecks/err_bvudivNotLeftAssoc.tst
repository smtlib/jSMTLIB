; Regression check: bvudiv is NOT :left-assoc (only bvand, bvor, bvadd, bvmul are,
; per FixedSizeBitVectors.smt2) so it must stay strictly binary even though
; bvand/bvor/bvadd/bvmul now accept more than two arguments.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ BitVec 4))
(assert (= (bvudiv x y z) x))
