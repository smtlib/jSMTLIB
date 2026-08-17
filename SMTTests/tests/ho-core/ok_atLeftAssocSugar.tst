; SMT-LIB 2.7 Sec. 3.7.2: "the application operator @ is defined as left-associative,
; allowing the syntax (@ t1 t2 t3) to be used in place of the syntax (@ (@ t1 t2) t3)."
; f is properly curried, of sort (-> Int (-> Int Bool)), so (@ f x y) means
; (@ (@ f x) y) -- see ok_atCurriedExplicit.tst for the explicit form. Confirms the
; sugar and the explicit form reason identically: asserting the sugar form true and
; the explicit form's negation together is unsat.
(set-logic ALL)
(declare-fun f () (-> Int (-> Int Bool)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (@ f x y))
(check-sat)
(assert (not (@ (@ f x) y)))
(check-sat)
