; (_ +oo eb sb) and friends are only recognized when the FloatingPoint theory is
; loaded; without it, this falls through to the generic identifier lookup and fails.
(set-logic QF_LIA)
(assert (= (_ +oo 8 24) (_ +oo 8 24)))
