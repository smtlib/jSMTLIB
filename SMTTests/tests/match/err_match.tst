; match type-checking errors: unknown constructor, constructor sort mismatch,
; and incompatible body sorts across cases
(set-logic AUFLIA)
(declare-datatype Color ((red) (green) (blue)))
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-fun c () Color)
(declare-fun t () Tree)
(assert (match c ( ((unknown x y) true) )))
(assert (match c ( ((node l r) true) )))
(assert (match t ( (leaf true) ((node l r) 0) )))
