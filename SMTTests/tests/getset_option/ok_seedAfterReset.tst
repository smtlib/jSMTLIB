; OPTIONS: --seed 5
; After reset the random seed is again the one given with --seed, as at start (#194)
(set-logic QF_UF)
(reset)
(get-option :random-seed)
