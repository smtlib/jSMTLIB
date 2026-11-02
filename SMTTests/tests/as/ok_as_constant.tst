; (as c S) on a declared constant, both as a formula and as a term
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () Bool)
(declare-fun y () U)
(declare-fun f (Bool) U)
(assert (as x Bool))
(assert (= (as y U) (f (as x Bool))))
(assert (as true Bool))
(check-sat)
; Solver bugs (.bad goldens): smtinterpol-2.5 rejects (as c S) on a non-overloaded constant
; (allowed by SMT-LIB Remark 8); bitwuzla rejects it as an invalid identifier.
