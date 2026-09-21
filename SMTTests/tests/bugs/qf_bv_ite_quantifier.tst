; Issue #49: characterizes that QF_BV.validExpression()'s noQuantifiers() call already
; recurses into an ite's condition argument via ordinary tree traversal, rejecting a
; quantifier nested there the same as one anywhere else in the formula (no code change was
; needed for QF_BV itself, unlike QF_ABV's array-sort gap in the same issue).
(set-logic QF_BV)
(declare-const b (_ BitVec 4))
(assert (= (ite (forall ((y Bool)) y) b b) b))
(reset)
(set-logic QF_BV)
(declare-const b (_ BitVec 4))
(declare-const c Bool)
(assert (= (ite c b b) b))
