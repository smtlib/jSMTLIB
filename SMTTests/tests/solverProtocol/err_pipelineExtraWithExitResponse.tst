; OPTIONS: --solver generic --pipeline
; #149: output read together with exit's response is out of step and reported. This happens when a
; solver one response ahead answers the command before exit late (err_pipelineExtraBeforeExit.tst);
; here the stub answers exit with two responses in one write.
(set-logic QF_UF)
(exit)
