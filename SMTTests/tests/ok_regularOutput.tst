; test changing the regular output channel
(set-logic QF_UF)
(get-option :regular-output-channel)
(set-option :regular-output-channel "tempout")
(get-option :regular-output-channel)
(assert true)
(set-option :regular-output-channel "stdout")
(get-option :regular-output-channel)
(assert true)
