; A function declared over a sort parameter is polymorphic: it applies at every sort, and
; its instances are unrelated (SMT-LIB 2.7, Remarks 3 and 17), so f can be negation on Bool
; and successor on Int (sat). Treating A as a new sort makes these applications ill-sorted.
(set-info :smt-lib-version 2.7)
(set-option :produce-models true)
(set-logic ALL)
(declare-sort-parameter A)
(declare-fun f (A) A)
(declare-const b Bool)
(declare-const n Int)
(assert (= (f b) (not b)))
(assert (= (f n) (+ n 1)))
(assert b)
(assert (= n 2))
(check-sat)
(get-value ((f b) (f n)))
