(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun t () Tree)
^^^^^^^^^^^^^^^^^^^^^^^
(assert (match t ((leaf false) ((node _ _) true))))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
