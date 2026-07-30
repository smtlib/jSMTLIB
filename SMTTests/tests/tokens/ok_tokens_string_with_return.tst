; ok tokens with all the allowed characters
(set-logic QF_LIA)
; token with newline
(set-info :x |     
"';:{}[]()`,#| )
; string with newline
(set-info :x "     
|';:{}[]()`,#" )
