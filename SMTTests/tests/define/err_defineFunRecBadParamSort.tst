; define-fun-rec: a parameter's declared sort is invalid/unknown -- caught by
; checkSorts before the function symbol is even added to the symbol table (checkFcnRec
; returns immediately once checkSorts reports errors).
(set-logic QF_UF)
(define-fun-rec f ((x BadSort)) Bool true)
