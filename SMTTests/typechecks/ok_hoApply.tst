; The HO-Core theory (the "@" function-application combinator, and the "->" arrow
; sort constructor) is not part of any standard-defined SMT-LIB logic -- confirmed by
; checking every logic file under SMT/logics/: only ALL.smt2 lists HO-Core among its
; theories (SMT/logics/HO-Core.smt2 itself is the theory definition, not a logic). So
; ALL is the only logic under which "@" and "->" are reachable at all.
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(declare-fun x () Int)
(assert (@ f x))
