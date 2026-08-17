; A user-defined sort alias still enforces genuine width mismatches -- expanding an
; alias to check compatibility must not make every BitVec width look interchangeable.
(set-logic QF_BV)
(define-sort Word32 () (_ BitVec 32))
(define-sort Word16 () (_ BitVec 16))
(declare-fun x () Word32)
(declare-fun y () Word16)
(assert (= x (bvand x y)))
