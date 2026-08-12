; QF_LRA: (* (/ 3 x) y): isConst(/ 3 x) -> non-numeral denominator returns false
; (covers isConst line 39)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* (/ 3 x) y)))
