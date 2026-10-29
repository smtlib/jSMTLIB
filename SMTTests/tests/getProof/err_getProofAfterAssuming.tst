; SMT-LIB 2.7 4.2.7: get-proof is an error unless the most recent check had no assumptions (A63);
; solvers that answer it get .lenient goldens
(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (not p))
(check-sat-assuming (p))
(get-proof)
