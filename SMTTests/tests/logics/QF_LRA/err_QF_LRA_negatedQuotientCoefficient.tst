; QF_LRA's :extensions allow (* c x) and (* x c) only for a coefficient c: m, (- m), d, (- d), or (/ c n)
; with c an integer coefficient m or (- m). (- (/ 1 2)) and (- (- 2)) are not coefficients, so the first
; three products are outside the logic (#186); the last three terms are the in-logic spellings.
(set-logic QF_LRA)
(declare-const x Real)
(assert (= (* (- (/ 1 2)) x) 0.0))
(assert (= (* x (- (/ 1 2))) 0.0))
(assert (= (* (- (- 2)) x) 0.0))
(assert (= (* (/ (- 1) 2) x) 0.0))
(assert (= (- (* (/ 1 2) x)) 0.0))
(assert (< (- (/ 1 2)) x))
