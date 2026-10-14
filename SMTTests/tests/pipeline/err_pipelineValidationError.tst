; OPTIONS: --pipeline
; An error found before sending (a repeated parameter name) among commands sent without waiting:
; it is printed after the earlier responses and before the later ones.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(define-fun f ((a Int) (a Int)) Int a)
(declare-fun y () Int)
(check-sat)
