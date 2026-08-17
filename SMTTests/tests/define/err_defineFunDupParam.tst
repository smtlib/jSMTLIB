; define-fun: duplicate parameter names -- caught generically by TypeChecker.validate()
; (validateUniqueDeclarations) before the command reaches checkFcn at all, so this is
; identical across every solver backend. See ok_defineFunsRecDupParamOverload.tst for
; the one remaining path where checkFcn's own overload-based duplicate-parameter
; handling (symTable.add(entry, false, true), which silently allows the duplicate) is
; still actually reachable.
(set-logic QF_UF)
(define-fun f ((x Bool) (x Bool)) Bool x)
