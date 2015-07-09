; Checks a simple sat problem
(set-logic QF_UF)   	; success
(declare-fun P () Bool) 	; success
(assert P) 				; success
(assert (not P)) 		; success
(check-sat)				; unsat ; Result should be $expected, not $actual
(exit)					; success

