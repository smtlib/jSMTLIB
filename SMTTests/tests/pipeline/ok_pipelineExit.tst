; OPTIONS: --pipeline
; exit after commands sent without waiting: their responses come first, and nothing after
; exit is executed.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(exit)
(check-sat)
