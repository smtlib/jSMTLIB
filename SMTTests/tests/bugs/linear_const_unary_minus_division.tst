; Issue #45: a unary minus wrapping a division, e.g. (- (/ 1 2)), must be recognized as a
; linear-arithmetic constant by LRA.isConst()/Logic.isRealConst() -- a constant coefficient of
; -1/2 times a free variable is a linear term and must not be rejected as nonlinear.
(set-logic QF_LRA)
(declare-const x Real)
(assert (= (* (- (/ 1 2)) x) 0.0))
(reset)
(set-logic AUFLIRA)
(declare-const y Real)
(assert (< (- (/ 1 2)) y))
