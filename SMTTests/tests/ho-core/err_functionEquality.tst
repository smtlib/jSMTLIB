; (= f g) on declared functions is ill-sorted, so the assertion is rejected and the
; remaining assertions are sat (SMT-LIB 2.7 Remark 10)
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f 0) 1))
(assert (= (g 0) 2))
(assert (= f g))
(check-sat)
; Solver bugs (.bad goldens): z3 4.8.12 and later accept (= f g), treating functions as
; arrays; yices2 accepts it too (and answers unsat here).
