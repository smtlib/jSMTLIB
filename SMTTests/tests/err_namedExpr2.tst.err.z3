(assert (forall ((r Bool)) (! r :named R))) ; error
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(assert (exists ((r Bool)) (! r :named R))) ; error
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(assert (let ((r true)) (! r :named R))) ; error - R already defined
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(assert (forall ((q Bool)) (let ((r q)) (! r :named RRR)))) ; error - FIXME
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
