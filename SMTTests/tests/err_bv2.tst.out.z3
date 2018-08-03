success
success
success
success
(assert (= (bvnot x) #b1011))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 6 column 27: Sorts (_ BitVec 3) and (_ BitVec 4) are incompatible")
(assert (= (bvnot true) #b1011))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 7 column 22: operator is applied to arguments of the wrong sort")
(assert (= (bvnot x y) #b1011))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 8 column 21: declared arity mismatches supplied arity")
(assert (= (bvneg x) #b0111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 9 column 27: Sorts (_ BitVec 3) and (_ BitVec 4) are incompatible")
(assert (= (bvneg x y) #b0111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 10 column 21: declared arity mismatches supplied arity")
(assert (= (bvand true y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 11 column 24: operator is applied to arguments of the wrong sort")
(assert (= (bvand x false) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 12 column 25: Argument false at position 1 does not match declaration (declare-fun bvand ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvand x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 13 column 21: Argument y at position 1 does not match declaration (declare-fun bvand ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvand x y z) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 14 column 23: declared sorts do not match supplied sorts")
(assert (= (bvor x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 15 column 20: Argument y at position 1 does not match declaration (declare-fun bvor ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvadd x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 16 column 21: Argument y at position 1 does not match declaration (declare-fun bvadd ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvmul x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 17 column 21: Argument y at position 1 does not match declaration (declare-fun bvmul ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvshl x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 18 column 21: Argument y at position 1 does not match declaration (declare-fun bvshl ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvlshr x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 19 column 22: Argument y at position 1 does not match declaration (declare-fun bvlshr ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvudiv x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 20 column 22: Argument y at position 1 does not match declaration (declare-fun bvudiv ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (= (bvurem x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 21 column 22: Argument y at position 1 does not match declaration (declare-fun bvurem ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))")
(assert (bvult x y))
^^^^^^^^^^^^^^^^^^^^
(error "line 22 column 18: Argument y at position 1 does not match declaration (declare-fun bvult ((_ BitVec 3) (_ BitVec 3)) Bool)")
(assert (bvult y))
^^^^^^^^^^^^^^^^^^
(error "line 23 column 16: declared arity mismatches supplied arity")
(assert (bvult true y))
^^^^^^^^^^^^^^^^^^^^^^^
(error "line 24 column 21: operator is applied to arguments of the wrong sort")
(assert (bvult x false))
^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 25 column 22: Argument false at position 1 does not match declaration (declare-fun bvult ((_ BitVec 3) (_ BitVec 3)) Bool)")
(assert (= (concat x y) #xa))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 26 column 27: Sorts (_ BitVec 8) and (_ BitVec 4) are incompatible")
(assert (= (concat y) #xaa))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 27 column 26: Sorts (_ BitVec 5) and (_ BitVec 8) are incompatible")
(assert (= (concat x true) z))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 28 column 25: invalid concat application")
(assert (= ((_ extract 40 2) z) x))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 29 column 30: invalid extract application")
(assert (= ((_ extract 1 2) z) x))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 30 column 29: invalid extract application")
(assert (= ((_ extract a 1) z) x))
                       ^
(error "Expected a numeral here, instead of a symbol")
(assert (= ((_ extract ) z) x))
                       ^
(error "Expected a numeral here, instead of a )")
(assert (= ((_ extract 1 2 3 ) z) x))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 31 column 31: invalid extract application")
(assert (= #b101 #b1010))
^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 32 column 23: Sorts (_ BitVec 3) and (_ BitVec 4) are incompatible")
(assert (distinct #b1 #b10))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 33 column 26: Sort mismatch between first argument and argument 2")
(assert (ite true #b0 #b11))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 34 column 26: Sorts (_ BitVec 1) and (_ BitVec 2) are incompatible")
