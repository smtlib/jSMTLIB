; (_ to_fp eb sb) overload (a): a single (_ BitVec eb+sb) argument reinterprets the raw
; bits as a FloatingPoint value of that same width -- +zero's bit pattern is all zeros.
(set-logic ALL)
(declare-fun b () (_ BitVec 32))
(assert (= b (_ bv0 32)))
(assert (= ((_ to_fp 8 24) b) (_ +zero 8 24)))
(check-sat)
