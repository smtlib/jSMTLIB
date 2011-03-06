; get-proof after sat/unknown
(set-option :produce-proofs true)
(set-logic QF_UF)
(assert false)
(check-sat)
(get-proof)
