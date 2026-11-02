; #58: a solver-reported line number is the line of this file on which the failing command
; starts, whatever lines jSMTLIB adds, omits or joins when sending the script
(set-option :print-success true)
(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun x () Bool)


(declare-fun x () Bool)
(set-option :regular-output-channel "stdout")
(declare-fun x () Bool)
(echo "hello")
(declare-fun x () Bool)
(get-option :print-success)
(declare-fun x () Bool)
(get-option :produce-models)
(declare-fun x () Bool)
(declare-fun
    x () Bool)
(declare-fun x () Bool) (declare-fun x () Bool)
(push 1)
(declare-fun y () Bool)
(declare-fun y () Bool)
(pop 1)
; a comment
; on two lines
(declare-fun x () Bool)
(define-fun-rec f ((a Bool)) Bool a)
(declare-fun x () Bool)
(check-sat)
(get-assignment)
(declare-fun x () Bool)
(reset)
(set-logic ALL)
(declare-fun x () Bool)
(declare-fun x () Bool)
(assert z)
