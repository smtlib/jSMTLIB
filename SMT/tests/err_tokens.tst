; checks parsing of bad tokens
(set-logic QF_UF)
(assert #b )
(assert # )
(assert #q )
(assert #x )
(assert #b2 )
(assert #xzz )

(assert 00)
(assert 01)
(assert 01.2)
(assert 0.000) ; OK
(assert 0.0) ; OK
(assert 0. ) ; FIXME - needs a better error message

(assert true :[] a) ; FIXME - bad error message

(assert (! true :named a[] )) ; FIXME - needs a better error message
(assert (! true :named |a\b| )) ; FIXME - needs a better error message

(set-info :x "as\d" ); OK
(set-info :x 0a); 

(assert .123)

(assert , ) ; FIXME - in general change 'Invalid characters' erro rmessage to 'Invalid token'

(declare-fun .123 () Bool)
(declare-fun @asd () Bool)

