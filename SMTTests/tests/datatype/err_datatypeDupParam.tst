; declare-datatypes: duplicate sort parameter in par clause
(set-logic ALL)
(declare-datatypes ((Pair 2)) ((par (X X) ((pair (a X) (b X))))))
