; checks that set-logic is not allowed once in assert state
(set-logic QF_UF)                    ; success
(set-logic QF_UF)                    ; ERROR
(exit)                               ; success

