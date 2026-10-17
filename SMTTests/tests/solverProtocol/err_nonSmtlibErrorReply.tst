; OPTIONS: --solver generic
; Issue #118: a reply that is not SMT-LIB and begins with an invalid token (bitwuzla's
; "[error] ..." form) is reported as an error, not a crash. "generic" names no configured
; solver, so the generic adapter (Solver_smt) talks to the stub.
(set-logic QF_UF)
(assert true)
(check-sat)
