; @ (HO-Core function application) in its base, non-sugared 2-argument form.
; Merges typechecks/ok_atArity2.tst and typechecks/ok_hoApply.tst (identical content,
; kept as two files there for two different narrations) into one, and adds a genuine
; sat/unsat reasoning pair: (@ f x) and (not (@ f x)) can't both hold for the same f,
; x, which requires actual congruence/functional-application reasoning, not just
; parsing.
;
; HO-Core (the "@" combinator and the "->" arrow sort constructor) is not part of any
; standard-defined SMT-LIB logic -- confirmed by checking every logic file under
; SMT/logics/: only ALL.smt2 lists HO-Core among its theories. So ALL is the only
; logic under which "@" and "->" are reachable at all.
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(declare-fun x () Int)
(assert (@ f x))
(check-sat)
(assert (not (@ f x)))
(check-sat)
