; Float16/Float32/Float64/Float128 are true synonyms for the corresponding
; (_ FloatingPoint eb sb) sort (FloatingPoint.smt2's :notes) -- interchangeable in
; equality and freely mixable as arguments to fp.* operators, not merely
; independent same-named sorts. 3.0 is exact in every one of these formats.
(set-logic ALL)
(declare-fun a () Float16)
(declare-fun b () (_ FloatingPoint 5 11))
(declare-fun c () Float32)
(declare-fun d () (_ FloatingPoint 8 24))
(declare-fun e () Float64)
(declare-fun f () (_ FloatingPoint 11 53))
(declare-fun g () Float128)
(declare-fun h () (_ FloatingPoint 15 113))
(assert (= a b))
(assert (= c d))
(assert (= e f))
(assert (= g h))
(assert (= c ((_ to_fp 8 24) RNE 3.0)))
(assert (fp.leq c c d))
(assert (fp.eq (fp.add RNE c c) ((_ to_fp 8 24) RNE 6.0)))
(assert (fp.isNormal c))
(assert (= (fp.to_real c) 3.0))
(check-sat)
