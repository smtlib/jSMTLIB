; OPTIONS: --seed 42
; --seed reaches the solver: as :random-seed where the solver uses that option; z3 ignores it,
; so z3 4.5 and later get smt.random_seed (z3 4.3 gets -rs:, which no option reports).
(get-option :random-seed)
(get-option :smt.random_seed)
