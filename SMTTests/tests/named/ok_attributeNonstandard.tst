; Non-standard attributes on a term, with and without a value, are allowed
(set-logic QF_UF)
(assert (! true :my-attr 5))
(assert (! true :my-attr))
(check-sat)
