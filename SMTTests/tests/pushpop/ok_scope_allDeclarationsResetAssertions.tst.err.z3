(declare-sort S 1)
^^^^^^^^^^^^^^^^^^
(define-sort T () Bool)
^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun s () (S Int))
^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun t () T)
^^^^^^^^^^^^^^^^^^^^
(assert (and k f g t (= s s)))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-sort S 2)
^^^^^^^^^^^^^^^^^^
(define-sort T () Real)
^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun s () (S Int Int))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun t () T)
^^^^^^^^^^^^^^^^^^^^
(assert (= (+ k f g t) 0.0))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
