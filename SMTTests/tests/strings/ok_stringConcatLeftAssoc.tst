; str.++ is :left-assoc. "a" ++ "b" ++ "c" = "abc" -- pure constants.
(set-logic ALL)
(assert (= (str.++ "a" "b" "c") "abc"))
(check-sat)
(assert (= (str.++ "a" "b" "c") "abx"))
(check-sat)
