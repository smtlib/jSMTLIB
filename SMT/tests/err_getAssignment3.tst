; get-assignment after an assertion set command
(set-option :produce-assignments true)
(set-logic QF_UF)
(assert true)
(check-sat)
(push 1)
(get-assignment)
