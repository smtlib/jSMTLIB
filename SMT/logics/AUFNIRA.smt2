(logic AUFNIRA

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli and Clark Barrett"
 :date "2010-05-12"

 :theories (Reals_Ints ArraysEx)

:language
 "Closed formulas built over arbitrary expansions of the Reals_Ints and
  ArraysEx signatures with free sort and function symbols.
 "

:extensions
 "For every operator op with declaration (op Real Real s) for some sort s,
  and every term t1, t2 of sort Int and t of sort Real, the expression 
  - (op t1 t) is syntactic sugar for (op (to_real t1) t)
  - (op t t1) is syntactic sugar for (op t (to_real t1))
  - (/ t1 t2) is syntactic sugar for (/ (to_real t1) (to_real t2))
 "

:notes
 "This logic properly extends the logic AUFLIRA by allowing non-linear
  (integer/real) operators such as  *, /, div, mod, and abs.
 "
)
