; OPTIONS: --solver altergo
; alt-ergo 2.6.3 sends no reply at all to (get-proof), so its adapter answers unsupported.
; The adapter first sends a priming set-option; the stub ends after its last reply.
(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (and p (not p)))
(check-sat)
(get-proof)
(echo "after get-proof")
