; :named with a non-symbol value, and :pattern with a non-sequence value
(set-logic QF_UF)
(assert (! true :named 5))
(assert (forall ((x Bool)) (! x :pattern x)))
