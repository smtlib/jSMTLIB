; A second set-logic after set-logic ALL is an error (as in err_setLogicTwice.tst). z3 4.3 is never
; sent ALL, so its adapter reports this case itself.
(set-logic ALL)
(set-logic QF_UF)
