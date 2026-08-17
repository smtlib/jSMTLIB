; ite's first argument (the condition) must have sort Bool -- distinct from
; tests/bv/err_bv2/err_bv2_iteBranchSortMismatch.tst, which covers the other ite
; check (the two branches must have matching sorts), not this one
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun x () X)
(assert (ite x true false))
