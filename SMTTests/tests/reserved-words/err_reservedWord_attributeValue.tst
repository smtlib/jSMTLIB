; a symbol attribute value may not be a reserved word, quoted or not
(set-logic QF_UF)
(set-info :foo let)
(set-info :foo |forall|)
(declare-const x Bool)
(assert (! x :named let))
(assert (! x :named |par|))
