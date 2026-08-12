; a match pattern's constructor must belong to the scrutinee's datatype
(set-logic AUFLIA)
(declare-datatype Color ((red) (green) (blue)))
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-fun c () Color)
(assert (match c ( ((node l r) true) )))
