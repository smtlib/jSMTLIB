; get-proof and get-unsat-core require check-sat to have returned unsat; here :status
; declares sat (and the assertion is genuinely satisfiable), so both commands must
; complain with a proper error, not silently fall through to "unsupported".
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(declare-fun p () Bool)
(set-info :status sat)
(assert p)
(check-sat)
(get-proof)
(get-unsat-core)
