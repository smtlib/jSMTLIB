; Under ALL, distinct bit-vector constants differ. Simplify's adapter translated them as
; uninterpreted constants and answered sat, so it rejects ALL.
(set-logic ALL)
(declare-fun a () (_ BitVec 3))
(assert (= a (_ bv5 3)))
(assert (= a (_ bv6 3)))
(check-sat)
