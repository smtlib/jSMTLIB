(logic QF_UF

 :smt-lib-version 2.7
 :smt-lib-release "2024-07-21"
 :written-by "Cesare Tinelli"
 :date "2010-04-14"
 :last-updated "2024-07-21"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2024-07-21 Updated to Version 2.7.
  2015-04-25 Updated to Version 2.5.
 "
 
 :theories ()  ; includes just Core theory

 :language 
 "Closed quantifier-free formulas built over an arbitrary expansion of
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


