; str.< is :chainable. "a" < "b" < "c" is true; "a" < "c" < "b" is false
; ("c" < "b" fails) -- pure constants, trivial to decide.
(set-logic ALL)
(assert (str.< "a" "b" "c"))
(check-sat)
(assert (str.< "a" "c" "b"))
(check-sat)
