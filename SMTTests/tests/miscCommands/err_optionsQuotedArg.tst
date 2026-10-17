; OPTIONS: --solver test -L "no such dir"
; Issue #109: a double-quoted argument in an OPTIONS directive is one argument,
; so the error names the whole path.
(set-logic QF_UF)
