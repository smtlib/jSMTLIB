; OPTIONS: --print
; --print reports a command that does not type-check, as usual, and prints the others (#205 item 46)
(set-logic QF_LIA)
(declare-const x Int)
(assert (+ x true))
(assert (> y 0))
(assert (> x   0))
