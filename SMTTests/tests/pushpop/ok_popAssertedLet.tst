; pop discards an assertion containing a let
(set-logic QF_UF)
(declare-const p Bool)
(push 1)
(assert (let ((a p)) a))
(pop 1)
(assert (not p))
