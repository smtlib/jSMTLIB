; A -> sort declared via :right-assoc sugar must be structurally equal to the same
; sort declared via explicit nesting -- confirmed both by type-checking (= would be a
; sort error otherwise) and by a check-sat.
(set-logic ALL)
(declare-fun f () (-> Int Int Int Bool))
(declare-fun g () (-> Int (-> Int (-> Int Bool))))
(assert (= f g))
(check-sat)
