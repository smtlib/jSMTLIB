; A -> sort declared via :right-assoc sugar must be structurally equal to the same
; sort declared via explicit nesting.
(set-logic ALL)
(declare-fun f () (-> Int Int Int Bool))
(declare-fun g () (-> Int (-> Int (-> Int Bool))))
(assert (= f g))
