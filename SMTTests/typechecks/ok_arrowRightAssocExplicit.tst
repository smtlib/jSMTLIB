; The nested/explicit form of the sort ok_arrowRightAssocSugar.tst's (-> Int Int
; Bool) sugar is meant to abbreviate -- confirms the underlying curried-sort machinery
; itself is fine; only the :right-assoc sugar for writing it with a flat argument list
; is missing.
(set-logic ALL)
(declare-fun f () (-> Int (-> Int Bool)))
