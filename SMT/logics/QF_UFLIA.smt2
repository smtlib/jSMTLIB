(logic QF_UFLIA

 :smt-lib-version 2.7
 :smt-lib-release "2024-07-21"
 :written-by "Cesare Tinelli"
 :date "2011-06-11"
 :last-updated "2024-07-21"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2024-07-21 Updated to Version 2.7.
  2015-04-25 Updated to Version 2.5.
 "

 :theories ( Ints )

 :language 
 "Closed quantifier-free formulas built over arbitrary expansions of the
  Ints signatures with free sort and function symbols, but with the 
  following restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, **, /, div, mod, and abs, except as specified in the 
    :extensions attributes;
 "

 :extensions
 "As in the logic QF_LIA."
)

