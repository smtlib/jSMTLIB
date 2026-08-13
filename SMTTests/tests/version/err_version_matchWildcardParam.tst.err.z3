(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun t () Tree)
^^^^^^^^^^^^^^^^^^^^^^^
(assert (match t ( ((node _ r) true) (leaf false) )))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
