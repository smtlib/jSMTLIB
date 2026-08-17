; A bvN literal (_ bvNNN size) is only recognized when the BitVector theory is loaded;
; without it, this falls through to the generic identifier lookup and fails there.
(set-logic QF_LIA)
(assert (= (_ bv3 4) (_ bv3 4)))
