; QF_RDL constants (QF_RDL.smt2): c is m or (- m) for a numeral m, and the :extensions form
; (op (- x y) (/ c n)) with n a nonzero numeral gives rational constants
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(assert (< (- x y) (/ 3 2)))
(assert (>= (- y x) (/ (- 7) 4)))
(assert (> (- y x) (- 2)))
(assert (> (- (+ x x) (+ y y)) 2))
(check-sat)
