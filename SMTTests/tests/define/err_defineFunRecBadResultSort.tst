; define-fun-rec: the declared result sort itself is invalid/unknown -- also caught by
; checkSorts before the symbol is added to the symbol table.
(set-logic QF_UF)
(define-fun-rec f ((x Bool)) BadSort x)
