; OPTIONS: --solver test
; (as f S) on a bit-vector or floating-point function: S must be the result sort
(set-logic ALL)
(declare-const x (_ BitVec 8))
(declare-const y Float32)
(assert (= ((as bvadd (_ BitVec 8)) x x) x))
(assert (= ((as bvadd (_ BitVec 16)) x x) x))
(assert ((as bvult Bool) x x))
(assert ((as bvult (_ BitVec 1)) x x))
(assert (= ((as fp.abs Float32) y) y))
(assert (= ((as fp.abs Float64) y) y))
(assert (= ((as (_ extract 3 0) (_ BitVec 4)) x) #x0))
(assert (= ((as (_ extract 3 0) (_ BitVec 8)) x) #x00))
