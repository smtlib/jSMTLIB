; QF_BV: quantifier-free bitvectors; no UF, no new sorts
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x #x00))
(assert (= y (bvadd x #x01)))
(assert (bvult x #xff))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyBV () (_ BitVec 8))
