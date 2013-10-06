success
success
success
(assert (forall ((r Bool)) (! r :named R))) ; error
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 5 column 40: invalid named expression, expression contains free variables")
(assert (exists ((r Bool)) (! r :named R))) ; error
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 6 column 40: invalid named expression, expression contains free variables")
success
(assert (let ((r true)) (! r :named R))) ; error - R already defined
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 8 column 37: named expression already defined")
success
success
(assert (forall ((q Bool)) (let ((r q)) (! r :named RRR)))) ; error - FIXME
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 11 column 54: invalid named expression, expression contains free variables")
