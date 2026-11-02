; OPTIONS: --relax
; with --relax, a nullary constructor pattern written in parentheses, (nil), draws a warning and is
; accepted (err_matchParenthesizedNullary.tst is the strict case); the command goes to the solver as written
(set-logic ALL)
(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-const l L)
(assert (match l (((nil) true) ((cons h t) false))))
(assert (= l nil))
(check-sat)
