; jSMTLIB's QF_FP combines Reals, FixedSizeBitVectors and FloatingPoint, so free constants of
; each sort are allowed. Split from tests/bugs/qf_fp_missing_restriction_class.tst (#89)
(set-logic QF_FP)
(declare-const r Real)
(declare-const bv (_ BitVec 8))
(declare-const f (_ FloatingPoint 8 24))
