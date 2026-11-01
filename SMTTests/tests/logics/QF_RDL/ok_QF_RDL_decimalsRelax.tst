; OPTIONS: --relax
; With --relax, jSMTLIB accepts a decimal d or (- d) as a QF_RDL constant, with a warning
; (err_QF_RDL_atoms.tst is the strict case)
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(assert (< (- x y) 1.5))
(assert (>= (- x y) (- 0.5)))
(assert (> (- (+ x x) (+ y y)) 2.5))
(check-sat)
