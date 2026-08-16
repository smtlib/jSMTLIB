; re.union's :left-assoc sugar still requires every argument to have sort RegLan -- b is Bool.
(set-logic ALL)
(declare-fun b () Bool)
(assert (str.in_re "b" (re.union (str.to_re "a") (str.to_re "b") b)))
