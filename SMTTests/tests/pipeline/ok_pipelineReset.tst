; OPTIONS: --pipeline
; reset sent without waiting; :smt-lib-version, allowed right after reset, waits.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(reset)
(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (< x 0))
(check-sat)
