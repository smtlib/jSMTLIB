; QF_UFIDL's :language: its Int symbols are numerals, binary - and +, <=, <, >=, >, and in
; every (op t1 t2) with op in {+, -} one of t1, t2 is a numeral
(set-logic QF_UFIDL)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
; neither argument is a numeral
(assert (= (+ x y) 3))
(assert (< (- x (f y)) 0))
(assert (= (f (- x y)) 0))
; (+ x 1 y) is (+ (+ x 1) y)
(assert (= (+ x 1 y) 0))
; Int symbols outside the logic
(assert (= (* 2 x) y))
(assert (= (- x) y))
(assert (= (div x 2) y))
(assert (= (mod x 2) y))
(assert (= (abs x) y))
