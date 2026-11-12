; A ; inside a quoted symbol begins no comment: the error on the next line is no line after a comment,
; so its column is corrected as any other (z3 before 5.1.0 counts one higher only after a comment, #196)
(set-logic QF_UF)
(declare-fun |a;b| () Bool)
(assert z)
