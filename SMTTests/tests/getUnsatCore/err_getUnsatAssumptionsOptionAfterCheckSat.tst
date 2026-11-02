; :produce-unsat-assumptions set only after check-sat-assuming (and after set-logic, where SMT-LIB
; makes it an error)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (not p))
(check-sat-assuming (p))
(set-option :produce-unsat-assumptions true)
(get-unsat-assumptions)
