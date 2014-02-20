; Tests whether the required options are settable
(set-option :print-success true)
(get-option :print-success)
(set-option :regular-output-channel "stdout")
(get-option :regular-output-channel)
(set-option :diagnostic-output-channel "stderr")
(get-option :diagnostic-output-channel)
(set-option :diagnostic-output-channel "stdout")
(get-option :diagnostic-output-channel)
(set-option :diagnostic-output-channel "tempout")
(get-option :diagnostic-output-channel)
; Skipping setting :print-success false because solvers differ on whether they then print success