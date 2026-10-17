; OPTIONS: --solver bitwuzla
; Issue #118 follow-up: the bitwuzla adapter keeps bitwuzla's own non-SMT-LIB error text
; and corrects its line number, which counts the adapter's priming line, to the script's.
(set-logic QF_UF)
(assert true)
(check-sat)
