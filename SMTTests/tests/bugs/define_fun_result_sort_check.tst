; Issue #40: Solver_test.define_fun() (via TypeChecker.checkFcn()) must reject a
; define-fun/define-fun-rec whose body's sort doesn't match the declared result sort, and
; must still accept a matching one.
(set-logic QF_UF)
(define-fun f () Bool 5)
(reset)
(set-logic QF_UF)
(define-fun-rec f () Bool 5)
(reset)
(set-logic QF_UF)
(define-fun f () Bool true)
