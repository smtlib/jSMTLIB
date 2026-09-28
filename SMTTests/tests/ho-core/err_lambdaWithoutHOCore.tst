; A lambda's own sort is the SMT-LIB 2.7 (-> sort+ sort) function sort, which is only
; declared by the optional HO-Core theory (see HO-Core.smt2's ":sorts ( (-> 2
; :right-assoc) )"). Under a logic that doesn't include HO-Core, "->" is simply an
; undeclared sort symbol -- so type-checking a lambda here fails the same honest way as
; using an explicit, undeclared (-> ...) sort would (see err_arrowWithoutHOCore.tst),
; not with a fabricated placeholder sort and not with a crash. See the design-decision
; comment on TypeChecker.visit(IExpr.ILambda) (jSMTLIB issue #125).
(set-logic QF_LIA)
(declare-fun g () Int)
(assert (= g (lambda ((x Int)) x)))
(check-sat)
