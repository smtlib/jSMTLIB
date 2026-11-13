; bvxnor is not :left-assoc (since 2020), so it takes exactly two arguments.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvxnor x x x)))
