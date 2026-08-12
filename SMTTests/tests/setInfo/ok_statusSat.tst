; Declaring :status sat before a satisfiable check-sat is consistent for any solver.
; For Solver_test specifically, this also demonstrates that it adopts :status as its
; check-sat result (it never actually proves anything on its own) -- which in turn
; unlocks get-model's precondition (only valid after check-sat returns sat or unknown).
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(set-info :status sat)
(assert p)
(check-sat)
(get-model)
