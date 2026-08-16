; SMT-LIB 2.7 Sec. 3.7.2: "the application operator @ is defined as left-associative,
; allowing the syntax (@ t1 t2 t3) to be used in place of the syntax (@ (@ t1 t2) t3)."
; f is properly curried, of sort (-> Int (-> Int Bool)), so (@ f x y) should mean
; (@ (@ f x) y), which works when written out explicitly -- see ok_atCurriedExplicit.tst.
;
; CURRENTLY FAILING: hits the same TypeChecker gap as ok_arrowRightAssocSugar.tst --
; visit(IFcnExpr)'s handling of Utils.AT just checks argSorts.size() != 2 outright,
; with no :left-assoc-sugar desugaring, matching its own
; "// FIXME - this is just here until we get par types implemented" comment.
(set-logic ALL)
(declare-fun f () (-> Int (-> Int Bool)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (@ f x y))
