; OPTIONS: --solver test
; jSMTLIB's test solver adopts :status unsat as its check-sat answer, after which get-proof is
; allowed: it answers unsupported.
(set-option :produce-proofs true)
(set-logic QF_UF)
(set-info :status unsat)
(assert false)
(check-sat)
(get-proof)
