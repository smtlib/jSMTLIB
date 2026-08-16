; @'s first argument must have a -> (arrow) sort -- see ok_hoApply.tst for why ALL is
; the only logic this is reachable under
(set-logic ALL)
(declare-fun f () Int)
(declare-fun x () Int)
(assert (@ f x))
