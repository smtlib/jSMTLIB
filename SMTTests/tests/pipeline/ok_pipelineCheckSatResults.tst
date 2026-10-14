; OPTIONS: --pipeline
; Several check-sats sent without waiting, with different answers, each followed by
; commands that change the assertions: each answer must be matched to its own check-sat.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= x 0))
(check-sat)
(pop 1)
(assert (< x 3))
(check-sat)
