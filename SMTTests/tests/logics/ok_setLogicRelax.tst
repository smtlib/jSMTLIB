; OPTIONS: --relax
; Under --relax, a second set-logic command is at least not rejected by jSMTLIB's own
; client-side "already set" gate (the same gate err_setLogicTwice.tst, same directory,
; confirms IS enforced without --relax) -- see that file's comment for why this whole
; branch (setLogicLocal's "logicSet != null" code) had no test at all before this pair.
; Kept deliberately minimal (no further commands after the second set-logic): several
; real solvers (cvc5, yices2, smtinterpol) have no client-side gate at all and forward
; every set-logic straight to their own process, which then separately, natively refuses
; a second one on its own terms regardless of --relax (smtinterpol: "Logic already
; set!"; yices2: "the logic is already set"; cvc5's parser treats it as fatal and exits
; the whole process) -- genuine, unrelated, solver-native behavior this test also ends up
; documenting, but not its point; anything past the second set-logic would just be
; further noise from that, not from Simplify's own client-side logic under test.
(set-logic QF_UF)
(declare-fun x () Bool)
(set-logic QF_UF)
