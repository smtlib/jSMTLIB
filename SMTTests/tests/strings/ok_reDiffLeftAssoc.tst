; re.diff is :left-assoc. {x,y,z} diff {y} diff {z} = {x}: "x" survives both
; subtractions, "y" is removed by the first.
(set-logic ALL)
(assert (str.in_re "x"
  (re.diff (re.union (str.to_re "x") (str.to_re "y") (str.to_re "z"))
           (str.to_re "y")
           (str.to_re "z"))))
(check-sat)
(assert (str.in_re "y"
  (re.diff (re.union (str.to_re "x") (str.to_re "y") (str.to_re "z"))
           (str.to_re "y")
           (str.to_re "z"))))
(check-sat)
