; define-fun after check-sat-assuming returns the solver to assert mode, where
; get-unsat-assumptions is an error (cvc5 aborts; z3 4.6 and later and SMTInterpol answer it, and
; yices2 answers wrongly; their adapters check)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat-assuming (p (not p)))
(define-fun r () Bool true)
(get-unsat-assumptions)
