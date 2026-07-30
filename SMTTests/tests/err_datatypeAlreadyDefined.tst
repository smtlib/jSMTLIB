; declare-datatype: constructor or selector name already defined
(set-info :smt-lib-version "V2.6")
(set-logic QF_UF)
(declare-fun f (Bool) Bool)
(declare-datatype D ((f (x Bool))))
(declare-fun g (Bool) Bool)
(declare-datatype E ((ctor (g Bool))))
