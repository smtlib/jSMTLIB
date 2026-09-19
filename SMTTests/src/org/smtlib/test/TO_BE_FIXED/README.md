# TO_BE_FIXED

Tests in this package **fail against the current code, on purpose.** Each one pins down a
real, tracked bug that hasn't been fixed yet, and is expected to keep failing until the
underlying issue is fixed.

They are **excluded from the normal test run** (`make test` / `make test-only` /
`bash runjunits`): `runjunits` still compiles everything here, so a change elsewhere can't
silently break these tests without at least a compile error, but it deliberately leaves them
out of the JUnitCore run list so a normal test run stays green.

Run one explicitly when you're working on its issue:

```
java -cp <classpath> org.junit.runner.JUnitCore org.smtlib.test.TO_BE_FIXED.<Name>
```

None of these represent an immediately crucial, user-visible break -- if they did, they'd be
fixed already. They're tracked here so the bug isn't forgotten and so a fix has an
immediate, ready-made regression test: write the fix, confirm the test now passes, then
**move the file into `org.smtlib.test.bugs`** (updating its package declaration) so it
rejoins the normal run, and close the corresponding issue.

## Current contents

| Test | Issue |
|---|---|

Keep this table in sync: add a row (with its issue link) whenever a new test lands here, and
remove the row when the test is fixed and moved back into `bugs/`.
