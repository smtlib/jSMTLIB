; OPTIONS: --relax --solver test
; --relax: a mismatch at a nullary declared argument sort names that sort, not a "sort family" (#236)
(set-logic QF_UFLIA)
(declare-fun par (A) (r A Int Bool))
(assert (r true 0))
(assert (r 0 true))
