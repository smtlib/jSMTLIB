; binary -'s :left-assoc sugar still requires every argument to have sort Real -- b is Bool.
(set-logic QF_LRA)
(declare-fun b () Bool)
(assert (= (- 5.0 2.0 b) 2.0))
