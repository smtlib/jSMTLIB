; Under ALL, no integer squares to 2. Simplify treats a nonlinear product as uninterpreted
; (answering sat), so its adapter rejects nonlinear products.
(set-logic ALL)
(declare-fun x () Int)
(assert (= (* x x) 2))
(check-sat)
