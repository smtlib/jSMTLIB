; Checks a simple sat problem
(set-logic QF_UF)   	; success
(declare-fun P () Bool) 	; success
(assert P) 				; success
(check-sat)				; sat ; Result should be $expected, not $actual
(exit)					; success

