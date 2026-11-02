; The index of (_ char H) has 1 to 5 hex digits, though leading zeros don't change the code point
(set-logic ALL)
(assert (= "A" (_ char #x000041)))
(assert (= "A" (_ char #x00041)))
