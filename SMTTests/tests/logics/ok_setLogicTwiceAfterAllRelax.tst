; OPTIONS: --relax
; Under --relax, a second set-logic after set-logic ALL is not rejected by the adapters' own gate
; (z3 4.3's adapter sends it, never having sent ALL); solvers that refuse it natively say so.
(set-logic ALL)
(set-logic QF_UF)
