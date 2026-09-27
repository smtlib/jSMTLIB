; A basic lambda term, (lambda ((x Int)) (+ x 1)): SMT-LIB 2.7ff, HO-Core theory
; (jSMTLIB issue #125). Confirms: parsing lambda as a term (alongside let/forall/exists/
; match); scoped type-checking of the parameter declarations and body (the parameter x is
; visible in the body, not outside it); the lambda's own computed sort, which is the
; SMT-LIB 2.7 (-> Int Int) function sort (not just the body's Int sort) -- matching a
; like-sorted declared function f, so (= f (lambda ...)) type-checks; and round-trip
; printing of the lambda term via get-assertions. See TypeChecker.visit(IExpr.ILambda)
; for how/when that (-> ...) result sort is actually computed. The push/pop around the
; assert also exercises the mock "test" solver's TypeChecker.clearSorts() walk (an
; IVisitor.TreeVisitor use) over a popped lambda-containing assertion.
(set-option :interactive-mode true)
(set-logic ALL)
(declare-fun f () (-> Int Int))
(push 1)
(assert (= f (lambda ((x Int)) (+ x 1))))
(get-assertions)
(pop 1)
