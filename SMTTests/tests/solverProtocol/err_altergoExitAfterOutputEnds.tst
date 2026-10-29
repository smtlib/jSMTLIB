; OPTIONS: --solver altergo
; alt-ergo exits after an error. Here its output ends (the stub closes it) while the process
; still runs, so exit is written to it and its response must not be waited for: the end of the
; output was already read while waiting for the echo after the assert.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(exit)
