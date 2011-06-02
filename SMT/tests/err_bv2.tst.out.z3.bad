success
success
success
success
(assert (= (bvnot x) #b1011))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl x :: bv[3]
#22 := (bvnot x)
(= #22 bv[11:4])

Expected sort: bv[3]
Actual sort:   bv[4]
Function sort: (define = bv[3] bv[3] bool).
ERROR: line 5 column 37: expression is not well sorted.")
(assert (= (bvnot true) #b1011))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 6 column 41: unknown; ERROR: Operator is applied to arguments of the wrong sort (bvnot true)
The arguments have sorts: bool")
(assert (= (bvnot x y) #b1011))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: unexpected number of arguments.
WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
#28 := (bvnot x y)
(= #28 bv[11:4])

Expected sort: bv[3]
Actual sort:   bv[4]
Function sort: (define = bv[3] bv[3] bool).
ERROR: line 7 column 39: expression is not well sorted.")
(assert (= (bvneg x) #b0111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl x :: bv[3]
#28 := (bvneg x)
(= #28 bv[7:4])

Expected sort: bv[3]
Actual sort:   bv[4]
Function sort: (define = bv[3] bv[3] bool).
ERROR: line 8 column 36: expression is not well sorted.")
(assert (= (bvneg x y) #b0111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: unexpected number of arguments.
WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
#28 := (bvneg x y)
(= #28 bv[7:4])

Expected sort: bv[3]
Actual sort:   bv[4]
Function sort: (define = bv[3] bv[3] bool).
ERROR: line 9 column 38: expression is not well sorted.")
(assert (= (bvand true y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 10 column 42: unknown; ERROR: Operator is applied to arguments of the wrong sort (bvand true y)
The arguments have sorts: bool bv[5]")
(assert (= (bvand x false) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl x :: bv[3]
(bvand x false)

Expected sort: bv[3]
Actual sort:   bool
Function sort: (define bvand bv[3] bv[3] bv[3]).
ERROR: line 11 column 42: expression is not well sorted.")
(assert (= (bvand x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvand x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvand bv[3] bv[3] bv[3]).
ERROR: line 12 column 38: expression is not well sorted.")
(assert (= (bvand x y z) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 1 of decl z :: bv[8]
decl y :: bv[5]
(bvand y z)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvand bv[3] bv[3] bv[3]).
ERROR: line 13 column 40: expression is not well sorted.")
(assert (= (bvor x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvor x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvor bv[3] bv[3] bv[3]).
ERROR: line 14 column 37: expression is not well sorted.")
(assert (= (bvadd x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvadd x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvadd bv[3] bv[3] bv[3]).
ERROR: line 15 column 38: expression is not well sorted.")
(assert (= (bvmul x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvmul x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvmul bv[3] bv[3] bv[3]).
ERROR: line 16 column 38: expression is not well sorted.")
(assert (= (bvshl x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvshl x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvshl bv[3] bv[3] bv[3]).
ERROR: line 17 column 38: expression is not well sorted.")
(assert (= (bvlshr x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvlshr x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvlshr bv[3] bv[3] bv[3]).
ERROR: line 18 column 39: expression is not well sorted.")
(assert (= (bvudiv x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvudiv x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvudiv bv[3] bv[3] bv[3]).
ERROR: line 19 column 39: expression is not well sorted.")
(assert (= (bvurem x y) #b111))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvurem x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvurem bv[3] bv[3] bv[3]).
ERROR: line 20 column 39: expression is not well sorted.")
(assert (bvult x y))
^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
(bvult x y)

Expected sort: bv[3]
Actual sort:   bv[5]
Function sort: (define bvult bv[3] bv[3] bool).
ERROR: line 21 column 21: expression is not well sorted.")
(assert (bvult y))
^^^^^^^^^^^^^^^^^^
(error "WARNING: unexpected number of arguments.
ERROR: line 22 column 19: expression is not well sorted.")
(assert (bvult true y))
^^^^^^^^^^^^^^^^^^^^^^^
(error "line 23 column 25: unknown; ERROR: Operator is applied to arguments of the wrong sort (bvult true y)
The arguments have sorts: bool bv[5]")
(assert (bvult x false))
^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl x :: bv[3]
(bvult x false)

Expected sort: bv[3]
Actual sort:   bool
Function sort: (define bvult bv[3] bv[3] bool).
ERROR: line 24 column 25: expression is not well sorted.")
(assert (= (concat x y) #xa))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
decl x :: bv[3]
#23 := (concat x y)
(= #23 bv[10:4])

Expected sort: bv[8]
Actual sort:   bv[4]
Function sort: (define = bv[8] bv[8] bool).
ERROR: line 25 column 40: expression is not well sorted.")
(assert (= (concat y) #xaa))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl y :: bv[5]
#23 := (concat y)
(= #23 bv[170:8])

Expected sort: bv[5]
Actual sort:   bv[8]
Function sort: (define = bv[5] bv[5] bool).
ERROR: line 26 column 39: expression is not well sorted.")
(assert (= (concat x true) z))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 27 column 38: unknown; ERROR: Could not obtain size for concatenation")
(assert (= ((_ extract 40 2) z) x))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of decl x :: bv[3]
decl z :: bv[8]
#23 := (extract[40:2] z)
(= #23 x)

Expected sort: bv[39]
Actual sort:   bv[3]
Function sort: (define = bv[39] bv[39] bool).
ERROR: line 28 column 42: expression is not well sorted.")
(assert (= ((_ extract 1 2) z) x))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 29 column 42: unknown; ERROR: Could not obtain size for extract")
(assert (= ((_ extract a 1) z) x))
                       ^
(error "Expected a numeral here, instead of a symbol")
(assert (= ((_ extract ) z) x))
                       ^
(error "Expected a numeral here, instead of a )")
(assert (= ((_ extract 1 2 3 ) z) x))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "line 30 column 44: unknown; ERROR: Could not obtain size for extract")
(assert (= #b101 #b1010))
^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 2 of (= bv[5:3] bv[10:4])

Expected sort: bv[3]
Actual sort:   bv[4]
Function sort: (define = bv[3] bv[3] bool).
ERROR: line 31 column 32: expression is not well sorted.")
success
(assert (ite true #b0 #b11))
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
(error "WARNING: Sort mismatch for argument 3 of (ite true bv[0:1] bv[3:2])

Expected sort: bv[1]
Actual sort:   bv[2]
Function sort: (define ite bool bv[1] bv[1] bv[1]).
ERROR: line 33 column 34: expression is not well sorted.")
