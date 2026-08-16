; re.inter is :left-assoc. {a,b} inter {b,c} inter {b,d} = {b}: "b" is in
; all three sets, "a" is only in the first.
(set-logic ALL)
(assert (str.in_re "b"
  (re.inter (re.union (str.to_re "a") (str.to_re "b"))
            (re.union (str.to_re "b") (str.to_re "c"))
            (re.union (str.to_re "b") (str.to_re "d")))))
(check-sat)
(assert (str.in_re "a"
  (re.inter (re.union (str.to_re "a") (str.to_re "b"))
            (re.union (str.to_re "b") (str.to_re "c"))
            (re.union (str.to_re "b") (str.to_re "d")))))
(check-sat)
