; Tests _ wildcard in match patterns (bare and in constructor params) in V2.7
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-fun t () Tree)
(assert (match t ((leaf false) ((node _ _) true))))
