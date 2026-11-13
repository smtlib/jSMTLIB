; OPTIONS: -q
; (reset) returns :print-success to its value at startup, false here as -q was given (#205 item 35)
(set-option :print-success true)
(set-logic QF_UF)
(reset)
(set-logic QF_UF)
(declare-const p Bool)
(check-sat)
