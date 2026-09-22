; Issue #49: QF_ABV's own :language mandates every array term have sort
; (Array (_ BitVec i) (_ BitVec j)) -- a BitVec-to-Bool array must be rejected, both as a
; direct declare-const and as a define-sort alias. Also characterizes that a quantifier
; nested inside an ite's condition is already rejected by ordinary recursive traversal.
(set-logic QF_ABV)
(declare-const arr (Array (_ BitVec 4) (_ BitVec 8)))
(reset)
(set-logic QF_ABV)
(declare-const arr (Array (_ BitVec 4) Bool))
(reset)
(set-logic QF_ABV)
(define-sort MyArr () (Array (_ BitVec 4) (_ BitVec 8)))
(reset)
(set-logic QF_ABV)
(define-sort BadArr () (Array (_ BitVec 4) Bool))
(reset)
(set-logic QF_ABV)
(declare-const b (_ BitVec 4))
(assert (= (ite (forall ((y Bool)) y) b b) b))
