; check-sat-assuming's literal-format restriction (SMT-LIB V2.6 and earlier: each
; assumption must be a bare symbol or (not symbol)) accepts a bare symbol
(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat-assuming (p))
