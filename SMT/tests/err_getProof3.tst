; get-proof after an assertionset command
(set-option :produce-proofs true)
(set-logic QF_UF)
(assert true)
(check-sat)
(push 1)
(get-proof)
