; Tests whether :print-success can be written and turns printing success off
(get-option :print-success)      ; value result
(set-option :print-success false) ; no sucess result
(get-option :print-success)      ; value result
(set-option :print-success true) ; sucess result
(get-option :print-success)      ; value result
(set-option :print-success false) ; no sucess result
(exit)                           ; no success result
