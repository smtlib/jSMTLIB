; OPTIONS: --seed 5
; --seed is set at startup with (set-option :random-seed 5); reset restores the default, 0 (#194)
(get-option :random-seed)
(set-logic QF_UF)
(reset)
(get-option :random-seed)
