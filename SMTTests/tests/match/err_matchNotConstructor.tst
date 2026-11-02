; the head of a constructor pattern must be a constructor of the scrutinee's datatype
(set-logic ALL)
(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-const l L)
(declare-fun f (Int) L)
(assert (match l (((f x) true) (_ false))))
