; OPTIONS: --relax
; With --relax, :expand-definitions, removed in SMT-LIB 2.5, is still accepted (#163 item 10)
(get-option :expand-definitions)
(set-option :expand-definitions true)
(get-option :expand-definitions)
(set-option :expand-definitions false)
(get-option :expand-definitions)
