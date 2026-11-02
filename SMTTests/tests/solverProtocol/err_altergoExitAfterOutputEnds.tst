; OPTIONS: --solver altergo
; Here alt-ergo's output ends (the stub closes it, after an error) while the process still runs,
; so exit is written to it and its response must not be waited for: the end of the output was
; already read while waiting for the echo after the assert. exit is then not answered success.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(exit)
