; Experiment: --relax allowing a user declare-fun to carry a function attribute
; (:left-assoc), a non-standard extension -- SMT-LIB's declare-fun grammar has no
; attribute* production. If accepted, myadd should behave as :left-assoc sugar allows
; (myadd 1 2 3) to mean (myadd (myadd 1 2) 3), an uninterpreted function of 3 arguments.
(set-logic QF_UFLIA)
(declare-fun myadd (Int Int) Int :left-assoc)
(assert (= (myadd 1 2 3) 6))
(check-sat)
