; -> propagates a sort error from its first (domain) argument correctly
(set-logic ALL)
(declare-fun f () (-> BadSort Bool))
