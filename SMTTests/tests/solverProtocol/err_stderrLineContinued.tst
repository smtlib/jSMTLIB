; OPTIONS: --solver generic
; A stderr line read unfinished with check-sat's reply is finished by text read with the next
; command, whose error is on stderr: that line's end is diagnostic, and only the error answers.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
