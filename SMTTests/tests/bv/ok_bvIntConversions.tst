; SMT-LIB 2.7 bitvector <-> integer conversions: ubv_to_int, sbv_to_int, (_ int_to_bv m)
(set-logic ALL)
(declare-fun b () (_ BitVec 8))
(assert (= b #xff))                                    ; unsigned 255, signed -1
(declare-fun n () Int)
(assert (= n (ubv_to_int b)))
(declare-fun m () Int)
(assert (= m (sbv_to_int b)))
(declare-fun c () (_ BitVec 8))
(assert (= c ((_ int_to_bv 8) 20)))                    ; 20 mod 256 = 20
(assert (not (and (= n 255) (= m (- 1)) (= c #x14))))
(check-sat)  ; result should be unsat
