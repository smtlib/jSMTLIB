; (_ to_fp eb sb)'s 2-arg form requires the second argument to be FloatingPoint, Real,
; or BitVec -- b is Bool, which matches none of the four to_fp overloads.
(set-logic ALL)
(declare-fun b () Bool)
(assert (= ((_ to_fp 8 24) RNE b) (_ +zero 8 24)))
