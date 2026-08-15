; declare-datatypes: arity k does not match number of sort parameters in par clause
(set-logic ALL)
(declare-datatypes ((Pair 2)) ((par (X) ((pair (a X))))))
