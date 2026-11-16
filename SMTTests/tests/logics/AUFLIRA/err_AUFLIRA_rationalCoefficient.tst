; AUFLIRA: a rational coefficient (/ c n) needs n other than 0; (+ 1 2) is not a coefficient
(set-logic AUFLIRA)
(declare-const x Real)
(assert (> (* (/ 1 3) x) 0.0))
(assert (> (* (/ 1 0) x) 0.0))
(assert (> (* (+ 1 2) x) 0.0))
