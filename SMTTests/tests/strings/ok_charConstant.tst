; (_ char H), the Strings theory's one-character string constants: H is a hexadecimal of 1-5 digits,
; at most #x2FFFF; leading zeros don't matter, and get-assertions prints the index as written.
(set-option :interactive-mode true)
(set-logic ALL)
(assert (= "A" (_ char #x41)))
(assert (= (_ char #x41) (_ char #x041) (_ char #x00041)))
(assert (= (str.len (_ char #x2FFFF)) 1))
(check-sat)
(get-assertions)
(assert (distinct (_ char #x2b) (_ char #x0002B)))
(check-sat)
