; check-sat-assuming with several assumptions, one of them not a symbol (z3 4.3 and 4.5 get them
; as a legacy check-sat)
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (=> p q))
(check-sat-assuming (p (not q) r))
(check-sat-assuming (p q (not r)))
