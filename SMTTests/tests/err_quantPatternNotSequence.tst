; a :pattern attribute value must be a sequence of terms, not a bare atom
(set-logic AUFLIA)
(declare-fun le (Int Int) Bool)
(assert (forall ((x Int)(y Int)) (! (le x y) :pattern 5)))
