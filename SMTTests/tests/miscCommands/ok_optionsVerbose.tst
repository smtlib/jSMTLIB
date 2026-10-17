; OPTIONS: --verbose 1 --solver test
; Issue #110: --verbose in an OPTIONS directive gives portable output. FileTests reads
; the properties before the directive's flags apply, and processCommandLine() does not
; read them again, so no "#reading properties" line (which embeds this checkout's jar
; path) is logged.
(set-logic QF_UF)
(check-sat)
