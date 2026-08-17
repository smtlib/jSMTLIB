; A user-defined sort alias for a BitVec sort (via define-sort) must be genuinely
; interchangeable with the (_ BitVec n) form it names -- isBitVec()/bitvecSize() need
; to expand() the alias first, the same fix FloatingPoint's Float16/32/64/128 needed.
; #x0000000F & #x000000FF = #x0000000F; #x0000000F & #x000000FF != #x00000000.
(set-logic QF_BV)
(define-sort Word32 () (_ BitVec 32))
(declare-fun x () Word32)
(assert (= x #x0000000F))
(assert (= (bvand x #x000000FF) #x0000000F))
(check-sat)
(assert (= (bvand x #x000000FF) #x00000000))
(check-sat)
