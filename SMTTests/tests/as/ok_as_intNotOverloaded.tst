; (as f S) is allowed for a symbol that is not overloaded, if S is its result sort (SMT-LIB Remark 8)
(set-logic QF_UFLIA)
(assert (= ((as + Int) 4 3) 1))
