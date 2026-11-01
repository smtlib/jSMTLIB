; Closes a coverage gap found while auditing Solver_simplify.java: its
; get_unsat_assumptions() has a "was the preceding check the right kind" guard
; (checkSatStatus == unsat) that does not actually distinguish check-sat from
; check-sat-assuming, even though its own error message claims the latter -- so a
; plain (unsat) check-sat, not check-sat-assuming, is enough to satisfy it and reach
; the method's real "unsupported" response, never previously exercised (see also
; Solver_test#get_unsat_assumptions, which Solver_simplify's version is a direct
; copy of -- same gap, same reachable "unsupported" tail).
;
; Real solvers vary since none of jSMTLIB's own precondition logic applies to them
; (each forwards straight to its native process); cvc5 and bitwuzla natively support
; get-unsat-assumptions after a plain check-sat and answer "()".
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(set-info :status unsat)
(assert false)
(check-sat)
(get-unsat-assumptions)
