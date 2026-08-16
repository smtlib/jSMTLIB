; The explicit/nested form of the application ok_atLeftAssocSugar.tst's
; (@ f x y) sugar is meant to abbreviate -- confirms the underlying curried-application
; machinery itself is fine (including that a partial application (@ f x) correctly
; gets an arrow-sorted result), only the :left-assoc sugar for the flat 3-argument
; syntax is missing.
(set-logic ALL)
(declare-fun f () (-> Int (-> Int Bool)))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun h () (-> Int Bool))
(assert (= (@ f x) h))
(assert (@ (@ f x) y))
