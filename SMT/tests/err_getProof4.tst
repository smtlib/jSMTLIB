; get-proof after sat/unknown
(set-option :produce-proofs true)
(set-logic QF_UF)
(assert true)
(check-sat)
(get-proof)
