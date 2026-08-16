; check-sat-assuming type-checks each assumption as Bool -- exercised only via
; Solver_test.check_sat_assuming's own TypeChecker.check() call (AbstractSolver's default,
; used by every real-solver adapter, just forwards the command text without calling it)
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun x () X)
(check-sat-assuming (x))
