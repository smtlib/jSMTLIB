; Under ALL, 7 div 2 is 3. Simplify treats div as uninterpreted (answering sat), so its
; adapter rejects div, mod and abs.
(set-logic ALL)
(assert (not (= (div 7 2) 3)))
(check-sat)
