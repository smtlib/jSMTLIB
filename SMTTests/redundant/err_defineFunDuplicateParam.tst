; define-fun's own parameter list must not have duplicate names. Distinct from
; tests/err_duplicateDeclParam.tst/err_duplicateLetBinding.tst (forall/exists/let bound
; variables, checked by TypeChecker's visit(IForall/IExists/ILet)) and
; tests/define/err_defineSort3.tst (define-sort's own type-parameter list) -- this is
; TypeChecker.validate()'s validateUniqueDeclarations, which nothing currently exercises
; for define-fun/define-fun-rec.
(set-logic QF_UF)
(define-fun f ((a Bool)(a Bool)) Bool a)
