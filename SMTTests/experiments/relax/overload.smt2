; Experiment: --relax allowing a user-declared function symbol to be overloaded (declared
; twice with different signatures) -- standard SMT-LIB only allows this for background-scope,
; theory-declared symbols, not user declare-fun. If accepted, (f (f x)) exercises resolving
; each occurrence of f to the overload matching its own argument's sort.
(set-logic QF_UFLIA)
(declare-fun f (Int) Bool)
(declare-fun f (Bool) Int)
(declare-fun x () Int)
(assert (f x))
(assert (= (f (f x)) 5))
(check-sat)
