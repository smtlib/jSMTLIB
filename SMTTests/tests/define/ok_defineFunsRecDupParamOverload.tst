; define-funs-rec: unlike define-fun/define-fun-rec, TypeChecker.validate() does not
; call validateUniqueDeclarations per-declaration for define-funs-rec, so a function
; with two identically-named parameters of different sorts reaches checkFcn, whose
; parameter loop adds each one with overload=true (symTable.add(entry, false, true)),
; silently allowing the duplicate rather than erroring. The body's use of x resolves to
; whichever overload type-checks -- here, the Bool-sorted x, since `and` requires Bool
; arguments.
(set-logic QF_UF)
(declare-sort A 0)
(define-funs-rec ((f ((x Bool) (x A)) Bool)) ((and x true)))
