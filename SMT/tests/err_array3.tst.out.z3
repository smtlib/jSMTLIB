success
(declare-sort Bool 0)
^^^^^^^^^^^^^^^^^^^^^
(error "line 3 column 19: sort already defined Bool")
(declare-sort Array 1)
^^^^^^^^^^^^^^^^^^^^^^
(error "line 4 column 14: invalid sort declaration, sort already declared/defined")
(declare-fun select () Bool)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 5 column 27: invalid declaration, builtin symbol select")
(declare-fun store () Bool)
^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 6 column 26: invalid declaration, builtin symbol store")
