z3 across versions gives inconsistent behavior for get-unsat-assumptions after a
plain (non-assuming) unsat check-sat with :produce-unsat-assumptions enabled --
z3-4.3 rejects with "only valid immediately after check-sat-assumptions returned
unsat", z3-4.5.0 rejects with "has not been enabled" (even though it was), and
z3-5.1.0 accepts and returns an empty list. This test exists to cover
Solver_simplify/AbstractSolver-side code paths, not to characterize z3's own
version-dependent quirks here -- see cvc5/yices2/smtinterpol/test for the
intended, consistent behavior this test actually checks.
