; check-sat-assuming's V2.6-and-earlier literal restriction: (not symbol) must have
; exactly one argument -- (not p q) does not qualify as a literal even though its
; head is "not"
(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(check-sat-assuming ((not p q)))
