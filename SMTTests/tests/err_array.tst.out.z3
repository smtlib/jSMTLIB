success
success
success
(declare-fun a () (Array I V))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 5 column 19: unknown sort 'Array'")
success
success
success
(assert (= v (select a i)))
^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 9 column 24: unknown function/constant select")
(assert (= a (store a i v)))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 10 column 25: unknown function/constant store")
