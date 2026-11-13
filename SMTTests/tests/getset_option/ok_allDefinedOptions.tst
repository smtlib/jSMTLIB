; Tests the defaults for the standard options on which every tested solver answers the default or unsupported; the others each have an ok_defaultOption_<option>.tst (#163 item 14).
(get-option :print-success)
(get-option :expand-definitions)
(get-option :produce-proofs)
(get-option :produce-unsat-cores)
(get-option :produce-assignments)
(get-option :global-declarations) ; new in V2.5
(get-option :produce-unsat-assumptions) ; new in V2.5
(get-option :reproducible-resource-limit) ; new in V2.5
