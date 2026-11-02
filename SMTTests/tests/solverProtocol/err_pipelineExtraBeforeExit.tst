; OPTIONS: --solver generic --pipeline
; #149: a solver one response ahead at the end of a script: exit takes the surplus 'success',
; and its own 'success', written after it, is reported as output out of step.
(set-logic QF_UF)
(declare-fun p () Bool)
(exit)
