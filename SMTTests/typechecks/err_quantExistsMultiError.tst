; ported from TypeCheckQuantifiers.checkBadExists. The original JUnit test calls
; TypeChecker.checkAssertion() directly and observes TWO errors from this one
; expression ("Unknown predicate symbol and with argument types X X" and "Unknown
; constant symbol t"). That can't be ported faithfully: Solver_test.assertExpr()
; only returns errs.get(0) -- the first error -- per its own
; "// FIXME - return all errors, not just the first" comment, so a normal (assert
; ...) command can only ever surface the first one. This is itself worth a
; dedicated test of that limitation (see phase (b)); here we just assert what a
; real (assert ...) command actually produces.
(set-logic AUFNIRA)
(declare-sort X 0)
(declare-fun p () Bool)
(declare-fun q () X)
(assert (exists ((r Bool)(s X)) (or (and s q) t)))
