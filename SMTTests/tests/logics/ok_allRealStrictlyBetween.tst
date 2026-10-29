; Under ALL, a real strictly between 0 and 1 exists. Simplify reasons over integers, so its
; adapter rejects reals.
(set-logic ALL)
(declare-fun r () Real)
(assert (and (< 0.0 r) (< r 1.0)))
(check-sat)
