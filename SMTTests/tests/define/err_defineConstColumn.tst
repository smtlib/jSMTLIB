; SMTInterpol and Alt-Ergo, which lack define-const, are sent the define-fun it abbreviates, spaced so that
; the solver's columns for the sort and the term are those of the source: z is at column 32
(set-logic QF_UF)
(define-const x Bool (and true z))
