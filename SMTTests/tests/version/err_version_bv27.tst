; OPTIONS: --solver test
; The bit-vector functions added in SMT-LIB 2.7 are errors under 2.6
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (bvnego x))
(assert (bvuaddo x x))
(assert (= (ubv_to_int x) 0))
(assert (= ((_ int_to_bv 4) 3) x))
(assert (= (bvneg x) x))
