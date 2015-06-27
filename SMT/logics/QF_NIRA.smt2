(logic QF_NIRA

 :smt-lib-version 2.0
 :written_by "David Cok, from AUFNIRA"
 :date "2015-06-27"

 :theories (Reals_Ints)

:language
 "Closed quantifier-free formulas built over arbitrary expansions of the Reals_Ints 
  signatures with free constant symbols.
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
