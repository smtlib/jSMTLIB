; Satisfiable QF_UF with an uninterpreted sort, function and predicate: a solver that decides
; QF_UF (Simplify included, #176) answers sat
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(assert (= (f a) b))
(assert (not (= a b)))
(assert (p (f a)))
(assert (not (p a)))
(check-sat)
