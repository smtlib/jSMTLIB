; A datatype may not take the name of an already declared sort.
(set-logic ALL)
(declare-sort S 0)
(declare-datatype S ((c)))
