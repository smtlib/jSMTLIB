; str.<= is :chainable. "a" <= "a" <= "b" is true; "b" <= "a" <= "c" is false
; ("b" <= "a" fails) -- pure constants, trivial to decide.
(set-logic ALL)
(assert (str.<= "a" "a" "b"))
(check-sat)
(assert (str.<= "b" "a" "c"))
(check-sat)
