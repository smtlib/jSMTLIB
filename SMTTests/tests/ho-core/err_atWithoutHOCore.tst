; @ is only registered when a logic's :theories includes HO-Core (see
; Utils.loadParFun) -- under a logic that doesn't, it's just an undeclared symbol, same
; as any other unknown function.
(set-logic QF_UF)
(declare-fun f () Bool)
(declare-fun x () Bool)
(assert (@ f x))
