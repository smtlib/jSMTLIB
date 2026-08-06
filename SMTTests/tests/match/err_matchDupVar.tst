; match error: duplicate variable in constructor pattern
(set-logic QF_UF)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-fun t () Tree)
(assert (match t ((leaf false) ((node x x) true))))
