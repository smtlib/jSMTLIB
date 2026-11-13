; bvxor is :left-assoc (QF_BV): (bvxor a b c) means (bvxor (bvxor a b) c).
; #b1100 ^ #b1010 = #b0110; #b0110 ^ #b1001 = #b1111.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvxor #b1100 #b1010 #b1001)))
(assert (= x #b1111))
(check-sat)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))
(declare-fun d () (_ BitVec 4))
(assert (distinct (bvxor a b c d) (bvxor (bvxor (bvxor a b) c) d)))
(check-sat)
