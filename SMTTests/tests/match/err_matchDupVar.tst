; match error: duplicate variable in constructor pattern
(set-info :smt-lib-version "V2.6")
(set-logic QF_UF)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-fun t () Tree)
(assert (match t ((leaf false) ((node x x) true))))
