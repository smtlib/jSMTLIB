; Checking that the value of :print-success can be set
(set-option :print-success false)  ;  ;
(get-option :print-success)        ; false ; Changed value of :print-success should be $expected, not $actual
(set-option :print-success true)   ; success ;
(get-option :print-success)        ; true ; Changed value of :print-success should be $expected, not $actual
