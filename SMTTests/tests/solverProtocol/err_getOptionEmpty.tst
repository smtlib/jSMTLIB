; OPTIONS: --solver generic
; An empty reply to get-option is an error: its value is a constant, a symbol, or a list.
; The generic adapter sends a priming set-option first.
(set-option :produce-models true)
(get-option :produce-models)
(get-option :produce-models)
