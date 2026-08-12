; get-model, get-value, and get-assignment require check-sat to have returned sat or
; unknown; here :status declares unsat (and the assertions are genuinely unsatisfiable),
; so all three commands must complain with a proper error, not silently fall through to
; "unsupported".
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-fun p () Bool)
(set-info :status unsat)
(assert p)
(assert (not p))
(check-sat)
(get-model)
(get-value ( p ))
(get-assignment)
