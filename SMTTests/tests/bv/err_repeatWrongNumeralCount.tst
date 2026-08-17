; (_ repeat n) takes exactly one numeral index
(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(assert (= #b1010 ((_ repeat 2 3) x)))
