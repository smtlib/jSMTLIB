(logic UF

 :smt-lib-version 2.0
 :written_by "David Cok, from QF_UF"
 :date "2015-06-27"
 
 :theories (Core)

 :language 
 "Closed formulas built over an arbitrary expansion of
  the Core signature with free sort and function symbols.
 "
 :values
 "For each sort other than Bool the set of values is abstract.
  For Bool it is defined as in the Core theory declaration.
 "
 :notes
 "Formulas can contain variables as long as they are bound by a let binder.
 "
 :notes
 "All the free symbols used in scripts for this logic must be declared in
  the scripts themselves.
 "
)


