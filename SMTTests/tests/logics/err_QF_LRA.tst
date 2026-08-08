; QF_LRA forbids quantifiers, nonlinear arithmetic, UF, and new sorts
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (forall ((z Real)) (>= z 0.0)))
(assert (= y (* x x)))
; UF declaration not allowed
(declare-fun g (Real) Real)
; new sort not allowed
(declare-sort S 0)
; division where dividend is not a constant (covers LRA.validExpression / error path)
(assert (= y (/ x 2.0)))
; (* (/ 3 0) x): isConst(/ 3 0) → division by zero returns false (covers isConst line 36)
(assert (= y (* (/ 3 0) x)))
; (* (/ 3 x) y): isConst(/ 3 x) → non-numeral denominator returns false (covers isConst line 39)
(assert (= y (* (/ 3 x) y)))
