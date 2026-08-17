; check-sat-assuming's "symbol or (not symbol)" literal restriction in V2.6 and
; earlier accepts the (not symbol) form -- see ok_checkSatAssumingLiteralSymbol.tst
; for the bare-symbol case, and err_version_checkSatAssumingLiteral.tst/Literal2.tst
; for rejected non-literal forms.
(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (not p))
(check-sat-assuming ((not p)))
