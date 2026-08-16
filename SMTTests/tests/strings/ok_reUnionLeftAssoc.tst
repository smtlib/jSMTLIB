; re.union is :left-assoc. The union of the singleton regexes for "a", "b",
; "c" matches exactly those three strings.
(set-logic ALL)
(assert (str.in_re "b" (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
(check-sat)
(assert (str.in_re "d" (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
(check-sat)
