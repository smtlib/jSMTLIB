(declare-datatype Color ((red) (green) (blue)))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun c () Color)
^^^^^^^^^^^^^^^^^^^^^^^^
(declare-fun t () Tree)
^^^^^^^^^^^^^^^^^^^^^^^
(assert (match c ( (red true) (green false) (blue false))))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(assert (match t ( (leaf true) ((node l r) false))))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
