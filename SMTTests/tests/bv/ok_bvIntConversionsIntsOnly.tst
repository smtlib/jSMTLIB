; OPTIONS: --solver test -L tests/bv/logics
; ubv_to_int, sbv_to_int and int_to_bv need the Ints theory (or Reals_Ints), not Reals_Ints only
(set-logic BV_INTS)
(declare-const x (_ BitVec 4))
(assert (= (ubv_to_int x) (sbv_to_int x)))
(assert (= ((_ int_to_bv 4) 3) x))
(check-sat)
