; Under ALL, the identity map differs from the successor map. Simplify's adapter translated
; lambda as nothing (answering sat), so it rejects maps.
(set-logic ALL)
(assert (= (lambda ((x Int)) x) (lambda ((x Int)) (+ x 1))))
(check-sat)
