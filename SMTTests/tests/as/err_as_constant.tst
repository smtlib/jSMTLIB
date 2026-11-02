; (as c S) on a constant is checked: c must be declared and S must be its sort
(set-logic QF_UF)
(declare-fun x () Bool)
(declare-sort U 0)
(assert (as x Bool))
(assert (as zzz Bool))
(assert (= (as x U) (as x U)))
; Solver bugs (.bad goldens): smtinterpol-2.5 rejects (as c S) on a non-overloaded constant
; (allowed by SMT-LIB Remark 8); bitwuzla rejects it as an invalid identifier.
