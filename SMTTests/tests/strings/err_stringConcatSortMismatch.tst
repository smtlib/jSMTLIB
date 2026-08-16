; str.++'s :left-assoc sugar still requires every argument to have sort String -- b is Bool.
(set-logic ALL)
(declare-fun b () Bool)
(assert (= (str.++ "a" "b" b) "ab"))
