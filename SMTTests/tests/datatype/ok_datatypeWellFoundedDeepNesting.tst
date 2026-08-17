; Exercises anyDeltaInSort/anyDeltaNotInSet's for-loop over a genuinely multi-parameter,
; non-recursive sort (rather than a bare 0-arity leaf or an immediate head-symbol match) --
; "data"'s doubly-nested (Array Int (Array Int Int)) sort requires both helpers to iterate
; past a first non-matching parameter to a second, rather than short-circuiting immediately
; or trivially exiting an empty loop. "node" is listed before "leaf" so the well-foundedness
; scan actually visits node's selectors (including the recursive "left"/"right" ones) before
; "leaf" alone would otherwise short-circuit the fixed-point pass.
(set-logic ALL)
(declare-datatype Tree ((node (data (Array Int (Array Int Int))) (left Tree) (right Tree)) (leaf)))
(declare-fun t () Tree)
(assert (= t t))
