; get-assertions after an assertion the solver rejected lists only the accepted ones (Simplify, which
; rejects the Real sort, lists the rejected one too: .bad)
(set-option :produce-assertions true)
(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(assert (< 0.5 1.5))
(get-assertions)
