; a bare identifier pattern that is not a nullary constructor of the scrutinee's
; datatype is treated as a catch-all variable binding, not an unknown constructor --
; this makes the match exhaustive even though not every constructor is listed.
(set-logic ALL)
(declare-datatype Color ((red) (green) (blue)))
(declare-fun c () Color)
(assert (match c ((red true) (other false))))
(check-sat)
