success
(declare-fun x Bool)
               ^^^^
(error "Expected a left parenthesis here, instead of a symbol")
(declare-fun x () A)
^^^^^^^^^^^^^^^^^^^^
(error "line 3 column 18: unknown sort 'A'")
(declare-fun x (y z) Bool)
^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 4 column 16: unknown sort 'y'")
(declare-fun x ((y Bool)(y Bool)) Bool)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 5 column 17: unknown sort 'y'")
(declare-fun x () A A)
                    ^
(error "Too many arguments or extraneous material after the command or missing right parenthesis")
