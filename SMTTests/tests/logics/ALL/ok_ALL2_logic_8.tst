; Using ALL logic with bit-vectors and integers
; 8-bit so as to run much faster
(set-option :produce-models true)
(set-logic ALL)
(declare-fun b () (_ BitVec 8))
(define-fun bb () (_ BitVec 8) (bvneg (bvand (bvneg b) #xf0))) ; rounds up to multiple of 16
(declare-fun n () Int )
(assert (= n  (ubv_to_int b)))
(declare-fun nn () Int  )
(assert (= nn (ubv_to_int bb)))
(assert (bvult b #xf0))
(assert (not (and (>= nn n) (>= (+ n 15) nn) (= (mod nn 16) 0) )))
(check-sat)  ; result should be unsat
