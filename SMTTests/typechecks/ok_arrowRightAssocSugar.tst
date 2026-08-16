; SMT-LIB 2.7 Sec. 3.7.2: "-> is defined as right-associative, allowing for instance
; the syntax (-> t1 t2 t3) to be used in place of the syntax (-> t1 (-> t2 t3))." So
; this declares f with the same sort as (declare-fun f () (-> Int (-> Int Bool))),
; which works -- see ok_arrowRightAssocExplicit.tst.
;
; CURRENTLY FAILING: TypeChecker.visit(ISort.IApplication) only ever checks the sort
; constructor's own fixed arity (args.size() != def.intArity()) and has no general
; mechanism honoring a theory-declared :right-assoc/:left-assoc/:chainable/:pairwise
; annotation (SMT-LIB Sec. 3.6.2) for anything beyond a handful of hardcoded built-in
; operators (and/or/bvand/etc.) -- new theory-declared symbols like HO-Core's -> and @
; don't get it. See ok_atLeftAssocSugar.tst for the corresponding @ case of the same gap.
(set-logic ALL)
(declare-fun f () (-> Int Int Bool))
