; :pattern requires a sequence of terms
(set-logic QF_UF)
(assert (forall ((x Bool)) (! x :pattern x)))
