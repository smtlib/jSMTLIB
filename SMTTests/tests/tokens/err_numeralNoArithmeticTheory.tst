; A plain integer numeral has no sort at all unless an arithmetic theory (Ints or
; Reals_Ints) is installed by the active logic. QF_UF installs neither. Distinct from
; tests/tokens/err_tokens.tst's coverage of the analogous decimal-literal case
; ((assert 0.000) etc. under QF_UF) -- nothing exercises a well-formed plain integer
; literal under a no-arithmetic logic.
(set-logic QF_UF)
(assert (= 1 1))
