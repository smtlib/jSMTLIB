; Issue #121, companion case: a comment missing its leading ';' isn't recognized as a
; comment at all -- its words are lexed as ordinary bare tokens, which used to be
; silently skipped while hunting for the next '(' (see err_strayIdentifierAsCommand.tst
; for the isolated case). Here the stray run sits between two otherwise-valid commands:
; only the first stray token is reported (matching the existing "skip to the next '('"
; recovery, which now also reports what it found before skipping), and the following
; command still executes normally once the parser resyncs.
(set-logic QF_UF)
(declare-const x Bool)
missing a semicolon here
(assert x)
