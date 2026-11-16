; OPTIONS: --relax --solver test
; --relax: a par constant whose sort does not use the parameter is determined without as;
; so is a constant overloaded with a function of the same name
(set-logic ALL)
(declare-fun par (A) (c Int))
(assert (= c 1))
(declare-fun g (Int) Int)
(declare-fun g () Int)
(assert (= g 1))
