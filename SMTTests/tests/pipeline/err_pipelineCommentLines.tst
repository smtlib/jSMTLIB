; OPTIONS: --pipeline
; Comments are passed to the solver between commands sent without waiting, so the line
; number in a solver's error message is still that of the script.
(set-logic QF_LIA)
; a comment
(declare-fun x () Int)
; two
; comments
(push 1)
(pop 2)
; another comment
(declare-fun y () Int)
(check-sat)
