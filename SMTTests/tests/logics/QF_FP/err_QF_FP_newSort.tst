; QF_FP forbids new sorts. Split from tests/bugs/qf_fp_missing_restriction_class.tst
; (#89: QF_FP had no restriction class, so quantifiers, declared functions and new sorts
; were accepted)
(set-logic QF_FP)
(declare-sort S 0)
