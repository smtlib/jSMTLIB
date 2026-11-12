; OPTIONS: --solver z3-4.3
; As ok_stderrLineUnfinishedExit, for the z3-4.3 adapter, whose exit logs it too (#194): a stderr line read unfinished with a reply, then not finished before exit, is still logged.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(exit)
