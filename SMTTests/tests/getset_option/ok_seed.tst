; OPTIONS: --seed 42
; --seed is set at startup with :random-seed (#194); z3 ignores that option (#202), so z3 4.5 and later
; also get smt.random_seed (z3 4.3 gets -rs:, which no option reports).
(get-option :random-seed)
(get-option :smt.random_seed)
