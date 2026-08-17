; define-sort: duplicate sort parameter in the parameter list -- caught generically by
; TypeChecker.validate() (validateUniqueSortParams) before the command is ever
; dispatched to any solver, so this is identical across every backend. This shadows
; checkSortAbbreviation's own older duplicate-parameter check (its "Duplicate sort
; parameters: ..." message, only reachable from the built-in "test" solver's
; define_sort handler), which the newer generic check now always catches first.
(set-logic QF_UF)
(define-sort MySort (T T) T)
