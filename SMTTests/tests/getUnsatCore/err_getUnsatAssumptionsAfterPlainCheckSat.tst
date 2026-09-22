; Closes a coverage gap found while auditing Solver_simplify.java: its
; get_unsat_assumptions() has a "was the preceding check the right kind" guard
; (checkSatStatus == unsat) that does not actually distinguish check-sat from
; check-sat-assuming, even though its own error message claims the latter -- so a
; plain (unsat) check-sat, not check-sat-assuming, is enough to satisfy it and reach
; the method's real "unsupported" response, never previously exercised (see also
; Solver_test#get_unsat_assumptions, which Solver_simplify's version is a direct
; copy of -- same gap, same reachable "unsupported" tail).
;
; Real solvers vary widely here since none of jSMTLIB's own precondition logic
; applies to them (each forwards straight to its native process): yices2/smtinterpol
; both reject setting :produce-unsat-assumptions after set-logic outright (a
; genuine, unrelated solver-native restriction) and so never even get to try;
; cvc5 natively supports get-unsat-assumptions after a plain check-sat and answers
; "()"; bitwuzla's behavior is not captured here -- see the .skip.bitwuzla file.
(set-logic QF_UF)
(set-info :status unsat)
(set-option :produce-unsat-assumptions true)
(assert false)
(check-sat)
(get-unsat-assumptions)
