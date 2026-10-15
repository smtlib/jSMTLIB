; OPTIONS: --pipeline
; Commands checked against the most recent check-sat answer (get-value, get-assignment,
; get-unsat-core) right after a check-sat sent without waiting:
; that answer must have been read first.
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-option :produce-unsat-cores true)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (! (= x 3) :named a))
(check-sat)
(get-value (x))
(get-assignment)
(push 1)
(assert (! (< x 0) :named b))
(check-sat)
(get-unsat-core)
(pop 1)
(check-sat)
(get-value (x))
