; :verbosity is a solver option: it does not turn on jSMTLIB's own diagnostic output (--verbose), and a
; reset does not change --verbose either (#205 item 35)
(set-option :verbosity 1)
(set-logic QF_UF)
(declare-const p Bool)
(reset)
(set-logic QF_UF)
(echo "done")
