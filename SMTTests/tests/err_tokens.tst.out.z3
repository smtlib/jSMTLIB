success
(assert #b )
        ^^
(error "Invalid token: #b")
(assert # )
        ^
(error "Invalid token: #")
(assert #q )
        ^^
(error "Invalid token: #q")
(assert #x )
        ^^
(error "Invalid token: #x")
(assert #b2 )
        ^^^
(error "Invalid token: #b2")
(assert #xzz )
        ^^^^
(error "Invalid token: #xzz")
(assert 00)
        ^^
(error "Incorrect format for a number - no leading zeros allowed: 00")
(assert 01)
        ^^
(error "Incorrect format for a number - no leading zeros allowed: 01")
(assert 01.2)
        ^^^^
(error "Incorrect format for a number - no leading zeros allowed: 01.2")
(assert 0.000) ; OK
^^^^^^^^^^^^^^
(error "line 3 column 13: invalid assert command, term is not Boolean")
(assert 0.0) ; OK
^^^^^^^^^^^^
(error "line 4 column 11: invalid assert command, term is not Boolean")
(assert 0. ) ; FIXME - needs a better error message
        ^^
(error "Invalid token: 0.")
(assert true :[] a) ; FIXME - bad error message
             ^^^
(error "Invalid token: :[]")
(assert true :[] a) ; FIXME - bad error message
             ^^^
(error "Too many arguments or extraneous material after the command or missing right parenthesis")
(assert (! true :named a[] )) ; FIXME - needs a better error message
                        ^^
(error "Invalid token: []")
(assert (! true :named |a\b| )) ; FIXME - needs a better error message
                       ^^
(error "Bar(|)-enclosed symbol is not terminated: |a")
(assert (! true :named |a\b| )) ; FIXME - needs a better error message
                         ^^^
(error "Invalid token: \b|")
success
(set-info :x 0a); 
             ^^
(error "Invalid token: 0a")
(assert .123)
^^^^^^^^^^^^^
(error "line 8 column 8: unknown constant .123")
(assert , ) ; FIXME - in general change 'Invalid characters' erro rmessage to 'Invalid token'
        ^
(error "Invalid token: ,")
(declare-fun .123 () Bool)
             ^^^^
(error "User-defined symbols may not begin with . or @")
(declare-fun @asd () Bool)
             ^^^^
(error "User-defined symbols may not begin with . or @")
