; -> is only registered as a sort when a logic's :theories includes HO-Core (see
; Utils.loadTheory's :sorts loop) -- under a logic that doesn't, it's just an undeclared
; sort symbol, same as any other unknown sort.
(set-logic QF_UF)
(declare-sort A 0)
(declare-fun f () (-> A A))
