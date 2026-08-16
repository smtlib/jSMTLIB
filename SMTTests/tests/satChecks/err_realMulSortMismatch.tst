; *'s :left-assoc sugar still requires every argument to have sort Real -- b is Bool.
(set-logic QF_LRA)
(declare-fun b () Bool)
(assert (= (* 2.0 3.0 b) 6.0))
