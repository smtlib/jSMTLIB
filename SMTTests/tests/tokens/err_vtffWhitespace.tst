; vertical tab and form feed are not SMT-LIB white space: an error (read as white space), and the command is not run
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(asserta)
(assert (notb))
; a vertical tab  in a comment is fine
(assert (and a b))
