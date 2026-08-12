; (* (- x) y) is nonlinear because (- x) is not an integer constant
; (covers Logic.isInteger false branch)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= z (* (- x) y)))
