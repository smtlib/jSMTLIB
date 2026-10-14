; OPTIONS: --pipeline
; Commands sent without waiting, in a logic every solver supports (bitwuzla supports no
; integer logic), with check-sat answers that differ and a get-value after a check-sat.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
; a comment
(assert (or p q))
(check-sat)
(push 1)
(assert (not p))
(assert (not q))
(check-sat)
(pop 1)
(assert (not q))
(check-sat)
(get-value (p q))
