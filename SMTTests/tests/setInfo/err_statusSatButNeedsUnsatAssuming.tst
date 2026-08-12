; get-unsat-assumptions requires check-sat-assuming to have returned unsat; here :status
; declares sat (and the assertion is genuinely satisfiable), so it must complain with a
; proper error, not silently fall through to "unsupported".
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-fun p () Bool)
(set-info :status sat)
(assert p)
(check-sat-assuming ( p ))
(get-unsat-assumptions)
