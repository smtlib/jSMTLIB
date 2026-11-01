; QF_IDL valid expressions
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
; symbol op symbol
(assert (>= x y))
(assert (<= x y))
(assert (> x y))
(assert (< x y))
; difference op positive numeral
(assert (>= (- x y) 3))
(assert (<= (- x y) 3))
(assert (> (- x y) 0))
(assert (< (- x y) 0))
; difference op zero
(assert (>= (- x y) 0))
; difference op negated numeral
(assert (>= (- x y) (- 3)))
(assert (<= (- x y) (- 5)))
(assert (> (- x y) (- 1)))
(assert (< (- x y) (- 7)))
; boolean connectives over IDL atoms
(assert (and (>= (- x y) 3) (<= (- y x) 5)))
(assert (or (>= x y) (>= y x)))
(assert (not (> x y)))
; define-sort alias is allowed (covers checkSortDeclaration pass path)
(define-sort MyInt () Int)
