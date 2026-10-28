; The value of :pattern must be a sequence of terms
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (> (f x) 0) :pattern)))
(assert (forall ((x Int)) (! (> (f x) 0) :pattern 5)))
