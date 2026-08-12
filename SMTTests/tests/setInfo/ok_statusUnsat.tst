; Declaring :status unsat before an unsatisfiable check-sat is consistent for any solver.
; For Solver_test specifically, this also demonstrates that it adopts :status as its
; check-sat result -- which in turn unlocks get-unsat-core's precondition (only valid
; immediately after check-sat returns unsat).
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(declare-fun p () Bool)
(set-info :status unsat)
(assert p)
(assert (not p))
(check-sat)
(get-unsat-core)
