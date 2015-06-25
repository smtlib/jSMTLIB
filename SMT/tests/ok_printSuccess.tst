; Tests whether :print-success can be written and turns printing success off
(get-option :print-success)      ; value result
(set-option :print-success false) ; no success result
(get-option :print-success)      ; value result
(set-option :print-success true) ; success result
(get-option :print-success)      ; value result
(set-option :print-success false) ; no success result
(exit)                           ; no success result
