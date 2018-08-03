success
success
success
(assert (forall ((x Int)(y Int)(z Int)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le x true))  )))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 5 column 107: Sort mismatch at argument #2 for function (declare-fun le (Int Int) Bool) supplied sort is Bool")
(assert (forall ((x Int)(y Int)(z Int)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le yy yy))  )))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 6 column 100: unknown constant yy")
