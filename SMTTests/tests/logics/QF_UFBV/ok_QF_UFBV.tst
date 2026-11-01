; QF_UFBV: quantifier-free bitvectors with UF and new sorts allowed
(set-logic QF_UFBV)
(declare-sort Tag 0)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bitvector operations
(assert (= x #x00))
(assert (= y (bvadd x #x01)))
(assert (= y (bvneg x)))
(assert (bvult x #xff))
; UF declaration is allowed
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= y (f x)))
