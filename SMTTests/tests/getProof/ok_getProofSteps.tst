; get-proof with a multi-step proof; printed compactly, one element per line for a list of lists
(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (and p q))
(assert (not p))
(check-sat)
(get-proof)
