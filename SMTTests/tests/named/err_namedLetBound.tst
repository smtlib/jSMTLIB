; A let-bound variable from outside a :named term is free in it, so the term is not closed: an error,
; a warning with --relax (whether the let is expanded first is an SMT-LIB ambiguity, #227)
(set-logic QF_UF)
(assert (let ((y true)) (! (and y y) :named b)))
