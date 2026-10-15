; OPTIONS: --pipeline
; A parse error among commands sent without waiting: the parser reports it as it reads,
; yet it is printed after the earlier responses.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (> x #z1))
(declare-fun y () Int)
(check-sat)
