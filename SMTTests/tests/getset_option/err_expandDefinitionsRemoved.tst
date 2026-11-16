; SMT-LIB 2.5 removed :expand-definitions, so from 2.5 on it is an unknown option, answered unsupported
; (without --relax: see ok_expandDefinitionsRelax); a solver that accepts it is lenient (#163 item 10)
(get-option :expand-definitions)
(set-option :expand-definitions true)
(get-option :expand-definitions)
