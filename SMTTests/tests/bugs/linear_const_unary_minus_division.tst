; Issue #45: a unary minus wrapping a division, e.g. (- (/ 1 2)), is a constant term. In AUFLIRA,
; (/ 1 2) of two Ints is (/ (to_real 1) (to_real 2)) by the :extensions (#211; #111 for solvers
; that reject it). (In the LRA logics (- (/ 1 2)) is a term but not a coefficient for *:
; logics/QF_LRA/err_QF_LRA_negatedQuotientCoefficient.tst, #186.)
(set-logic AUFLIRA)
(declare-const y Real)
(assert (< (- (/ 1 2)) y))
