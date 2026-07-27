; Tests successful get-option behavior including a set-then-get round trip
(get-option :verbosity) ; check default
(set-option :verbosity 2)
(get-option :verbosity)
