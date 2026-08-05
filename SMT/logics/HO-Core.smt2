(theory HO-Core

 :smt-lib-version 2.7
 :smt-lib-release "2025-02-05"
 :written-by "Clark Barrett, Pascal Fontaine, and Cesare Tinelli"
 :date "2025-02-05"
 :last-updated "2025-07-07"
 :update-history

 :sorts ( (-> 2 :right-assoc) )

 :funs ( (par (A B) (@ (-> A B :left-assoc) A B) ) )

 :definition
 "For every expanded signature Sigma, the instance of HO-Core with that signature
  is the theory consisting of all Sigma-models in which: 
  - the sort constructor -> denotes the map sort constructor, that is,
    for all sorts s1, s2 in Sigma, (-> s1 s2) denotes the full space of
    total functions from the domain denoted by s1 to the domain denoted by s2
  - for all sorts s1, s2 in Sigma, 
    (@ (-> s1 s2) s1 s2)
    denotes the function that returns the result of applying its first argument
    to its second.
 "

 :notes
 "Because of the semantics of -> the theory has extensionality, that is,
  for all sorts s1 and s2, the following formula holds:
  (forall ((f (-> s1 s2)) (g (-> s1 s2)))
    (= (= f g) (forall ((x s1)) (= (f x) (g x)))))
 "

 :values 
 "For all sorts s1, s2, the set of values for the sort (-> s1 s2) consists of
  - an abstract value for each map (from a countable subset of the maps)
    of type s1 -> s2;
  - terms of the form (lambda ((x s1)) t) where t has sort s2 when every
    free occurrence of x in t has sort s1.
 " 
)
