(assert (! p :named q)) ; conflicts with existing name
^^^^^^^^^^^^^^^^^^^^^^^
(assert (! q :named P)) ; conflicts
^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun P () Bool) ; conflicts
^^^^^^^^^^^^^^^^^^^^^^^
(assert (and (! p :named PP) (! q :named P))) ; second conflicts, first should be withdrawn
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
