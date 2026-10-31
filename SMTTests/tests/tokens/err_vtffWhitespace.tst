; vertical tab and form feed are not SMT-LIB white space: an error, then read as white space
(set-logic QF_UF)
(declare-consta Bool)
(declare-const bBool)
; a vertical tab  in a comment is fine
(assert (and a b))
