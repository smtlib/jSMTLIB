; QF_RDL atoms (QF_RDL.smt2 :language): the constant c is m or (- m) for a numeral m, so a
; decimal is rejected; a single-variable bound (op x c) is not an atom form; = is restricted
; like the other comparisons; repeated sums need equal lengths and take no (/ c n)
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(assert (= x (* 3 y)))
(assert (<= x 5))
(assert (>= (- x y) 1.5))
(assert (<= (- (+ x x) (+ y y y)) 1))
(assert (<= (- (+ x x) (+ y y)) (/ 1 2)))
(assert (<= (- x y) (/ 1 0)))
