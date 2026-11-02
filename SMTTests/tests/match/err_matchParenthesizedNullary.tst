; a nullary constructor pattern is written without parentheses: (nil) is not a pattern
(set-logic ALL)
(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-const l L)
(assert (match l (((nil) true) ((cons h t) false))))
