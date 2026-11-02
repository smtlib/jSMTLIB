; reset-assertions before set-logic is allowed and does nothing
(reset-assertions)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
