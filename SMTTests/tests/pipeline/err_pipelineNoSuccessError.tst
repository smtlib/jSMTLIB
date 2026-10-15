; OPTIONS: --pipeline
; With 'success' turned off, a solver error among pipelined commands is matched to its command
; and the later responses are not shifted.
(set-option :print-success false)
(set-logic QF_LIA)
(declare-fun x () Int)
(push 1)
(pop 2)
(declare-fun y () Int)
(assert (> x y))
(check-sat)
(assert (< y 0))
(check-sat)
