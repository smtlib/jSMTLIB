success
(declare-fun x Bool)
               ^^^^
(error "Expected a left parenthesis here, instead of a symbol")
(declare-fun x () A)
^^^^^^^^^^^^^^^^^^^^
(error "line 2 column 20: could not parse function declaration; ERROR: line 2 column 19: could not find sort  'A'.")
(declare-fun x (y z) Bool)
^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 3 column 27: could not parse function declaration; ERROR: line 3 column 17: could not find sort  'y'.")
(declare-fun x ((y Bool)(y Bool)) Bool)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 4 column 41: could not parse function declaration; ERROR: line 4 column 24: could not find sort symbol 'y'.")
(declare-fun x () A A)
                    ^
(error "Too many arguments or extraneous material after the command or missing right parenthesis")
