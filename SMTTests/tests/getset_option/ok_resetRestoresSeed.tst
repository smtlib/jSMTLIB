; OPTIONS: --seed 7
; (reset) returns every option to its default and then sends the command-line settings again, so --seed
; holds after it (#205 item 35)
(get-option :random-seed)
(reset)
(get-option :random-seed)
