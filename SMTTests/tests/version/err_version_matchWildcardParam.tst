; Tests version error: _ wildcard as a parameter in a structured match pattern
; requires SMT-LIB V2.7; bare _ wildcard is tested in err_version_matchWildcard.tst
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-fun t () Tree)
(assert (match t ( ((node _ r) true) (leaf false) )))
