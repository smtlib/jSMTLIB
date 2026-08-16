; re.++ is :left-assoc. The regex for "a" ++ "b" ++ "c" matches "abc" and
; nothing else -- checked via str.in_re rather than direct RegLan equality,
; since RegLan has no literal syntax of its own.
(set-logic ALL)
(assert (str.in_re "abc" (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
(check-sat)
(assert (str.in_re "abx" (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
(check-sat)
