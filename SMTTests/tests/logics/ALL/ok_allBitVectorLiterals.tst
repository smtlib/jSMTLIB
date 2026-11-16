; Under ALL, distinct bit-vector literals differ. Simplify's adapter rejects binary and hex literals
; (it has no bit-vectors).
(set-logic ALL)
(assert (distinct #b01 #b10))
(assert (= #x1 #x2))
(check-sat)
