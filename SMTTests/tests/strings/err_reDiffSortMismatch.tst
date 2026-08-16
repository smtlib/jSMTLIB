; re.diff's :left-assoc sugar still requires every argument to have sort RegLan -- b is Bool.
(set-logic ALL)
(declare-fun b () Bool)
(assert (str.in_re "x" (re.diff (str.to_re "x") (str.to_re "y") b)))
