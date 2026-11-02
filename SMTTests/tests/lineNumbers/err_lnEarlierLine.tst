; #58: a message naming the line of an earlier command (bitwuzla's "already defined at line")
; gives that command's line, with lines omitted and joined in between
(set-logic QF_UF)
(declare-fun x () Bool)

(declare-fun
    y () Bool)
(declare-fun x () Bool)
