; QF_ABV: quantifier-free bitvectors with arrays; no UF, no new sorts
(set-logic QF_ABV)
(declare-const x (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= x #x00))
(assert (= x (select a #x00)))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyBV () (_ BitVec 8))
