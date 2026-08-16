; -> propagates a sort error from its second (codomain) argument correctly
(set-logic ALL)
(declare-fun f () (-> Int BadSort))
