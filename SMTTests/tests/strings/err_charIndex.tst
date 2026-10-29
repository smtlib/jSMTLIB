; (_ char H) takes exactly one index, a hexadecimal
(set-logic ALL)
(assert (= "A" (_ char 65)))
(assert (= "A" (_ char A)))
(assert (= "A" (_ char #x41 #x42)))
(assert (= "A" (_ char #b1000001)))
