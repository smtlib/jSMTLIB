; QF_LRA: (* (/ 3 0) x): isConst(/ 3 0) -> division by zero returns false
; (covers isConst line 36)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* (/ 3 0) x)))
