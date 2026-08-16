; Experiment: --relax allowing a user script to declare a par-polymorphic function --
; standard SMT-LIB has no user-facing par syntax for functions at all (par only appears in
; declare-datatype's own constructor lists); this reuses exactly how a *theory* declares one,
; e.g. Core.smt2's (par (A) (= A A Bool :chainable)), as an alternate form of declare-fun
; (detected by the literal reserved word "par" where the function's own symbol normally
; goes). myeq is then usable at both Int and Bool, and :chainable lets it take more than its
; declared 2 arguments.
(set-logic QF_UFLIA)
(declare-fun par (A) (myeq A A Bool :chainable))
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (myeq a b 5))
(assert (myeq p q true))
(check-sat)
