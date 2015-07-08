; Checks that reset resets options, in particular :print-success
(set-logic QF_UF)					; success
(set-option :diagnostic-output-channel "temp") ; success
(set-option :print-success false)	; ;
(reset)								; ;
(get-option :print-success)         ; true ; after a reset, :print-success should be $expected, not $actual
(get-option :diagnostic-output-channel) ; "stderr" ; after a reset, :diagnostic-output-channel should be $expected, not $actual
