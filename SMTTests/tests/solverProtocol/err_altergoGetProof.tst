; OPTIONS: --solver altergo
; alt-ergo 2.6.3 writes nothing for a successful command, so the adapter sends an echo after each
; command and reads up to it; it also writes nothing for (get-proof), which the adapter answers
; unsupported without sending. The stub gives one reply line per command, a blank one for silence.
(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (and p (not p)))
(check-sat)
(get-proof)
(echo "after get-proof")
