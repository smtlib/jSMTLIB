#!/usr/bin/env python3
"""Probe each configured SMT solver's support for the standard, predefined
SMT-LIB 2.7 options (set-option/get-option) and info flags (get-info) and
emit a GitHub-flavored markdown table -- Options.md.

The SMT-LIB 2.7 language reference (Sections 3.8/3.9, Figures 3.8/3.9, and
4.1.7/4.1.8) defines a fixed set of *standard* option and info-flag keywords,
each explicitly marked `support: required` or `support: optional`. Solvers
may also accept arbitrary additional solver-specific options/flags, but
those aren't standardized so there's nothing to check them against; this
script covers only the standard, spec-defined set (14 options + 7 info
flags). See:
  https://smt-lib.org/papers/smt-lib-reference-v2.7-r2026-03-27.pdf
  (Section 4.1.7 "Solver options", Section 4.1.8 "Solver information")

Per the spec, a solver that does *not* implement a non-required option is
still required to respond correctly to get-option (returning the documented
default) while set-option for that option should report `unsupported`. So
each option gets two rows here:
  - "(get-option)"              -- does the solver answer the query at all,
                                    without erroring? (baseline protocol
                                    compliance, expected to pass regardless
                                    of whether the option is *implemented*)
  - "(set-option ...)"          -- does setting it to a non-default value
                                    actually take effect (verified by reading
                                    it back, and for the produce-* family, by
                                    actually invoking the command it's
                                    supposed to enable)? This is the row that
                                    answers "is it implemented".
Info flags are get-info-only (no analogous set), so they get one row each.

Grading:
  Y (yes)     - clean, error-free response with the expected effect.
  ~ (partial) - timed out, or produced ambiguous/unparseable output.
  N (no)      - explicit `unsupported`, an `(error ...)` response, or (for
                a *-option row) the readback shows the value never changed.

Usage:
  python3 options-report.py [--solver-dir DIR] [--solvers NAME[,NAME...]]
                             [--timeout SECONDS] [--out FILE]
"""

from __future__ import annotations

import argparse
import os
import platform
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

# ---------------------------------------------------------------------------
# Solver discovery (mirrors capability-report.py; kept standalone/duplicated
# so each script in this folder can be run independently)
# ---------------------------------------------------------------------------

SOLVER_FAMILIES = {
    "z3": ("z3-", False),
    "cvc5": ("cvc5-", False),
    "yices2": ("yices2-", False),
    "bitwuzla": ("bitwuzla-", False),
    "alt-ergo": ("alt-ergo-", False),
    "smtinterpol": ("smtinterpol-", True),
}

SOLVER_EXTRA_ARGS = {
    "cvc5": ["--quiet"],
}


def default_solver_dir() -> Path:
    system = platform.system().lower()
    machine = platform.machine().lower()
    if system == "darwin":
        p = "macos"
    elif system == "linux":
        p = "linux"
    elif system.startswith(("mingw", "msys", "cygwin", "windows")):
        p = "windows"
    else:
        p = system
    if machine in ("x86_64", "amd64", "i686"):
        a = "x64"
    elif machine in ("arm64", "aarch64"):
        a = "arm64"
    else:
        a = machine
    subdir = {
        ("macos", "x64"): "Solvers-macos",
        ("macos", "arm64"): "Solvers-macos-arm64",
        ("linux", "x64"): "Solvers-linux",
        ("linux", "arm64"): "Solvers-linux-arm64",
    }.get((p, a), "Solvers-windows" if p == "windows" else f"Solvers-{p}")
    here = Path(__file__).resolve().parent  # SMTTests/reports/
    return here.parent.parent.parent / "OpenJML21" / "Solvers" / subdir


def _version_key(name: str):
    return [int(n) for n in re.findall(r"\d+", name)]


def discover_solver_instances(solver_dir: Path, wanted=None) -> dict[str, list[tuple[str, Path, bool]]]:
    """Every matching binary for each solver family in solver_dir -- not just
    the newest -- as {family: [(version, path, is_jar), ...]} sorted oldest
    to newest."""
    found: dict[str, list[tuple[list[int], str, Path, bool]]] = {}
    if not solver_dir.is_dir():
        return {}
    for fname in sorted(os.listdir(solver_dir)):
        fpath = solver_dir / fname
        if not fpath.is_file():
            continue
        if fname.lower().endswith((".dll", ".lib", ".xml")):
            continue
        is_this_jar = fname.lower().endswith(".jar")
        base = fname[:-4] if fname.lower().endswith(".exe") else fname
        if is_this_jar:
            base = base[:-4]
        for display, (prefix, is_jar) in SOLVER_FAMILIES.items():
            if wanted and display not in wanted:
                continue
            if is_this_jar != is_jar:
                continue
            if not base.startswith(prefix):
                continue
            version = base[len(prefix):]
            found.setdefault(display, []).append((_version_key(base), version, fpath, is_jar))
    return {
        name: [(version, path, is_jar) for _key, version, path, is_jar in sorted(entries)]
        for name, entries in found.items()
    }


def solver_command(name: str, path: Path, is_jar: bool, smt2_file: Path) -> list[str]:
    if is_jar:
        cmd = ["java", "-jar", str(path)]
    else:
        cmd = [str(path)]
    cmd += SOLVER_EXTRA_ARGS.get(name, [])
    cmd.append(str(smt2_file))
    return cmd


def group_family_columns(family: str, instances: list[tuple[str, Path, bool]],
                          rows: list["Row"], results: dict) -> list[dict]:
    """Merge consecutive-by-version instances of one family whose results
    are identical across every row into a single report column, so e.g. nine
    z3 versions that all behave the same collapse to one column instead of
    nine. Only *adjacent* versions are merged (a later version that reverts
    to old behavior gets its own column, not silently re-merged)."""
    groups: list[dict] = []
    for version, path, is_jar in instances:
        vector = tuple(
            ((res.grade,) if row.version_varies else (res.grade, res.detail))
            if (res := results.get(((family, version), row.name))) else None
            for row in rows
        )
        if groups and groups[-1]["vector"] == vector:
            groups[-1]["versions"].append(version)
        else:
            groups.append({"vector": vector, "versions": [version], "path": path, "is_jar": is_jar})
    return groups


def column_label(family: str, versions: list[str]) -> str:
    if len(versions) == 1:
        return f"{family} {versions[0]}"
    return f"{family} {versions[0]}–{versions[-1]}"


# ---------------------------------------------------------------------------
# Row definitions
# ---------------------------------------------------------------------------


@dataclass
class Row:
    group: str  # "Options" or "Info flags"
    name: str
    support: str  # "required" or "optional", per the SMT-LIB 2.7 spec
    body: str  # SMT-LIB commands, after set-logic/declare preamble, no exit
    footnote: str = ""
    # True only for :version: its response is *expected* to differ between
    # every version of a family by construction, so that expected difference
    # must not be what stops two versions from grouping into one column --
    # only the pass/fail grade matters for this row's contribution to the
    # equivalence check, not the literal version string in the detail.
    version_varies: bool = False


ROWS: list[Row] = []


def add(group: str, name: str, support: str, body: str, footnote: str = "", version_varies: bool = False) -> None:
    ROWS.append(Row(group, name, support, body.strip() + "\n", footnote, version_varies))


REFERENCE_URL = "https://smt-lib.org/papers/smt-lib-reference-v2.7-r2026-03-27.pdf"

# ---- Options (Figure 3.8; support/defaults from Section 4.1.7) ------------

add("Options", ":diagnostic-output-channel (get-option)", "required",
    "(get-option :diagnostic-output-channel)")
add("Options", ":diagnostic-output-channel (set-option)", "required",
    '(set-option :diagnostic-output-channel "diag.tmp")',
    "Kept as the script's last command so a real channel switch can't "
    "divert the confirming response away from stdout.")

add("Options", ":print-success (get-option)", "required",
    "(get-option :print-success)",
    "Unlike every other row, this one deliberately does *not* enable "
    "print-success first (default is `false`), to see the solver's actual "
    "out-of-the-box default.")
add("Options", ":print-success (set-option)", "required",
    "(set-option :print-success true)\n(get-option :print-success)")

add("Options", ":regular-output-channel (get-option)", "required",
    "(get-option :regular-output-channel)")
add("Options", ":regular-output-channel (set-option)", "required",
    '(set-option :regular-output-channel "out.tmp")',
    "Kept as the script's last command; see the diagnostic-output-channel "
    "footnote.")

add("Options", ":global-declarations (get-option)", "optional",
    "(get-option :global-declarations)")
add("Options", ":global-declarations (set-option; functional)", "optional",
    """
(set-option :global-declarations true)
(push 1)
(declare-const x Int)
(pop 1)
(assert (= x 0))
(check-sat)
""",
    "Functional test: declares `x` inside a push/pop scope, then references "
    "it after the matching pop -- only well-defined if declarations are "
    "genuinely global, not scoped to the assertion-stack level.")

add("Options", ":interactive-mode (get-option)", "optional",
    "(get-option :interactive-mode)",
    "Deprecated alias for :produce-assertions (Section 4.1.7); tested only "
    "for the bare get/set round trip, not functionally.")
add("Options", ":interactive-mode (set-option)", "optional",
    "(set-option :interactive-mode true)\n(get-option :interactive-mode)")

add("Options", ":produce-assertions (get-option)", "optional",
    "(get-option :produce-assertions)")
add("Options", ":produce-assertions (set-option; functional)", "optional",
    """
(set-option :produce-assertions true)
(declare-const x Int)
(assert (> x 0))
(get-assertions)
""")

add("Options", ":produce-assignments (get-option)", "optional",
    "(get-option :produce-assignments)")
add("Options", ":produce-assignments (set-option; functional)", "optional",
    """
(set-option :produce-assignments true)
(declare-const p Bool)
(assert (! p :named p_named))
(check-sat)
(get-assignment)
""")

add("Options", ":produce-models (get-option)", "optional",
    "(get-option :produce-models)")
add("Options", ":produce-models (set-option; functional)", "optional",
    """
(set-option :produce-models true)
(declare-const x Int)
(assert (> x 0))
(check-sat)
(get-value (x))
""")

add("Options", ":produce-proofs (get-option)", "optional",
    "(get-option :produce-proofs)")
add("Options", ":produce-proofs (set-option; functional)", "optional",
    """
(set-option :produce-proofs true)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(get-proof)
""")

add("Options", ":produce-unsat-assumptions (get-option)", "optional",
    "(get-option :produce-unsat-assumptions)")
add("Options", ":produce-unsat-assumptions (set-option; functional)", "optional",
    """
(set-option :produce-unsat-assumptions true)
(declare-const x Int)
(assert (> x 0))
(check-sat-assuming ((< x 0)))
(get-unsat-assumptions)
""")

add("Options", ":produce-unsat-cores (get-option)", "optional",
    "(get-option :produce-unsat-cores)")
add("Options", ":produce-unsat-cores (set-option; functional)", "optional",
    """
(set-option :produce-unsat-cores true)
(assert (! (> 1 0) :named a1))
(assert (! (< 1 0) :named a2))
(check-sat)
(get-unsat-core)
""")

add("Options", ":random-seed (get-option)", "optional",
    "(get-option :random-seed)")
add("Options", ":random-seed (set-option)", "optional",
    "(set-option :random-seed 42)\n(get-option :random-seed)",
    "Only checks that the readback reflects the value set, not that the "
    "solver's randomization is actually reproducible run-to-run.")

add("Options", ":reproducible-resource-limit (get-option)", "optional",
    "(get-option :reproducible-resource-limit)")
add("Options", ":reproducible-resource-limit (set-option; functional)", "optional",
    """
(set-option :reproducible-resource-limit 1)
(declare-fun x () Real)
(assert (= (* x x) 6.25))
(assert (> x 0.0))
(check-sat)
""",
    "Functional, not a get-option readback: at least one solver accepts "
    "set-option and visibly honors the limit (forcing `unknown` on a query "
    "it can otherwise solve trivially -- see the ALL capability report's "
    "NRA row) while its get-option for this same keyword always reports "
    "`unsupported` regardless, which would have made a plain readback test "
    "wrongly grade it N. Graded Y only if this forces `unknown`; a solver "
    "that solves the (deliberately easy) query outright despite the limit "
    "is graded N here even though it may still honor the option under "
    "harder queries -- treat N as suggestive, not definitive.")

add("Options", ":verbosity (get-option)", "optional",
    "(get-option :verbosity)",
    "The spec defines no standard default for :verbosity, so a solver "
    "reporting `unsupported` or an implementation-specific default on this "
    "row isn't necessarily non-compliant.")
add("Options", ":verbosity (set-option)", "optional",
    "(set-option :verbosity 1)\n(get-option :verbosity)")

# ---- Info flags (Figure 3.9; support from Section 4.1.8) -------------------

add("Info flags", ":authors (get-info)", "required", "(get-info :authors)")
add("Info flags", ":error-behavior (get-info)", "required", "(get-info :error-behavior)")
add("Info flags", ":name (get-info)", "required", "(get-info :name)")
add("Info flags", ":version (get-info)", "required", "(get-info :version)",
    version_varies=True)

add("Info flags", ":all-statistics (get-info)", "optional",
    "(assert true)\n(check-sat)\n(get-info :all-statistics)",
    "Only allowed in sat/unsat mode (Section 4.1.8), hence the preceding "
    "check-sat.")
add("Info flags", ":assertion-stack-levels (get-info)", "optional",
    "(get-info :assertion-stack-levels)")
add("Info flags", ":reason-unknown (get-info)", "optional",
    """
(set-option :reproducible-resource-limit 1)
(declare-fun x () Real)
(assert (= (* x x) 6.25))
(assert (> x 0.0))
(check-sat)
(get-info :reason-unknown)
""",
    ":reason-unknown is only valid after a check-sat that actually returned "
    "`unknown` (Section 4.1.8). This forces that via a minimal "
    ":reproducible-resource-limit plus a nonlinear query, but a solver that "
    "either ignores the resource limit or is fast enough to solve it "
    "outright will legitimately not reach `unknown` -- in which case a "
    "correct `(error ...)` response to the mode violation grades as N here "
    "even though the solver isn't really at fault. Treat an N on this row "
    "as inconclusive, not a confirmed gap, unless you check the footnote "
    "detail.",
)


GROUP_ORDER = ["Options", "Info flags"]

# ---------------------------------------------------------------------------
# Running probes
# ---------------------------------------------------------------------------


@dataclass
class Result:
    grade: str  # "Y", "P", "N"
    detail: str = ""


def truncate(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    cut = text[:limit]
    space = cut.rfind(" ")
    if space > limit * 0.6:
        cut = cut[:space]
    return cut + "..."


def run_row(name: str, path: Path, is_jar: bool, row: Row, timeout: float, workdir: Path) -> Result:
    # No trailing (exit): with :print-success true, exit's own "success" ack
    # would become the new last line and bury the real query response
    # beneath it. All four locally-tested solvers terminate cleanly on EOF
    # without an explicit exit, so the script just ends after the last
    # command.
    script = f"(set-logic ALL)\n(set-option :print-success true)\n{row.body}"
    # :print-success's own get-option row intentionally starts from the
    # solver's real default instead of forcing it on first.
    if row.name.startswith(":print-success"):
        script = f"(set-logic ALL)\n{row.body}"

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", dir=workdir, delete=False
    ) as f:
        f.write(script)
        tmpname = f.name
    try:
        cmd = solver_command(name, path, is_jar, Path(tmpname))
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=workdir)
        except subprocess.TimeoutExpired:
            return Result("P", "timeout")
        except OSError as e:
            return Result("N", f"exec failed: {e}")

        stdout_lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip()]
        stderr_lines = [ln.strip() for ln in proc.stderr.splitlines() if ln.strip()]

        if not stdout_lines:
            reason = "no output"
            err_line = next((ln for ln in stderr_lines if "error" in ln.lower()), "")
            if err_line:
                reason = err_line
            elif proc.returncode != 0:
                reason = f"exit code {proc.returncode}"
            return Result("N", truncate(reason, 200))

        last = stdout_lines[-1]
        if last.lower() == "unsupported":
            return Result("N", "unsupported")
        # Match the actual SMT-LIB error response shape, `(error "...")`,
        # not a bare "error" substring -- several legitimate responses
        # contain "error" as part of a keyword, e.g. `(:error-behavior
        # continued-execution)` for the :error-behavior info flag itself.
        if re.match(r"^\(\s*error\b", last, re.IGNORECASE):
            return Result("N", truncate(last, 200))
        # This row's whole point is verifying that the resource limit
        # actually forces an early `unknown` on a query the solver could
        # otherwise solve outright -- any other clean response (e.g. `sat`)
        # means the limit had no visible effect on this query.
        if row.name.startswith(":reproducible-resource-limit (set-option"):
            if last == "unknown":
                return Result("Y")
            return Result("N", last)
        return Result("Y", last if len(last) < 60 else "")
    finally:
        try:
            os.unlink(tmpname)
        except OSError:
            pass


# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------

GRADE_SYMBOL = {"Y": "✅", "P": "⚠️", "N": "❌"}


def render_table(header: list[str], rows: list[list[str]]) -> list[str]:
    """Render a GitHub-markdown table with cells padded to a common column
    width, so it's readable as plain text (not just when rendered)."""
    all_rows = [header] + rows
    widths = [max(len(r[i]) for r in all_rows) for i in range(len(header))]

    def fmt_row(r: list[str]) -> str:
        return "| " + " | ".join(cell.ljust(widths[i]) for i, cell in enumerate(r)) + " |"

    lines = [fmt_row(header), "|" + "|".join("-" * (w + 2) for w in widths) + "|"]
    lines += [fmt_row(r) for r in rows]
    return lines


def render_markdown(
    columns: list[dict],
    results: dict[tuple[tuple[str, str], str], Result],
) -> str:
    lines = []
    lines.append("# SMT solver standard options & info-flags report")
    lines.append("")
    lines.append(
        "Generated by `SMTTests/reports/options-report.py`. The SMT-LIB 2.7 "
        "reference defines a fixed set of standard `set-option`/`get-option` "
        "options and `get-info` flags, each marked `support: required` or "
        f"`support: optional` (Sections 4.1.7/4.1.8: <{REFERENCE_URL}>). "
        "Solver-specific extensions beyond this standard set exist too, but "
        "aren't checked here since there's no spec to check them against."
    )
    lines.append("")
    lines.append(
        "Each optional item gets two rows: `(get-option)` tests baseline "
        "protocol compliance (a solver not implementing the option is still "
        "required to answer the query with the documented default, not an "
        "error), while `(set-option ...)` -- functional where practical -- "
        "tests whether the option is actually *implemented* (the value "
        "changes, and for produce-* options, the command it enables really "
        "works). A solver can legitimately be readable but not settable for "
        "an optional item; that's expected, not a bug."
    )
    lines.append("")
    lines.append(
        "Every version of z3/yices2 found alongside the current release is "
        "tested too, not just the newest. Consecutive versions of a family "
        "that answer every single row identically are merged into one "
        "column, labeled with the version range they cover (e.g. `z3 "
        "4.3.1–4.8.12`); a version that behaves differently -- even on "
        "just one row -- gets its own column."
    )
    lines.append("")
    lines += render_table(
        ["✅ works as documented", "⚠️ timeout / ambiguous", "❌ unsupported, error, or no effect"],
        [],
    )
    lines.append("")

    header = ["Group", "Item", "Spec support"] + [
        column_label(c["family"], c["versions"]) for c in columns
    ]

    footnotes: list[str] = []
    footnote_index: dict[str, int] = {}

    def footnote_marker(text: str) -> str:
        if text not in footnote_index:
            footnotes.append(text)
            footnote_index[text] = len(footnotes)
        return f"[^{footnote_index[text]}]"

    table_rows: list[list[str]] = []
    for group in GROUP_ORDER:
        for row in [r for r in ROWS if r.group == group]:
            cells = [group, row.name, row.support]
            for c in columns:
                label = column_label(c["family"], c["versions"])
                rep_version = c["versions"][0]
                res = results.get(((c["family"], rep_version), row.name))
                if res is None:
                    cells.append("—")
                    continue
                symbol = GRADE_SYMBOL[res.grade]
                # For :version, the detail (the literal version string) only
                # holds for rep_version, not the whole group -- skip it
                # rather than attribute one member's exact string to all.
                show_detail = res.detail and not (row.version_varies and len(c["versions"]) > 1)
                if show_detail:
                    note_text = f"**{label} / {row.name}**: {res.detail}"
                    symbol += footnote_marker(note_text)
                cells.append(symbol)
            if row.footnote:
                marker = footnote_marker(row.footnote)
                cells[1] += marker
            table_rows.append(cells)
    lines += render_table(header, table_rows)

    if footnotes:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append("### Footnotes")
        lines.append("")
        for i, text in enumerate(footnotes, 1):
            lines.append(f"[^{i}]: {text}")

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver-dir", type=Path, default=None, help="Directory containing solver binaries (default: auto-detected Solvers-<platform> next to this checkout)")
    ap.add_argument("--solvers", type=str, default=None, help="Comma-separated subset of solver names to test (default: all discovered)")
    ap.add_argument("--groups", type=str, default=None, help=f"Comma-separated subset of {{{', '.join(GROUP_ORDER)}}} to run (default: both)")
    ap.add_argument("--timeout", type=float, default=10.0, help="Per-row timeout in seconds (default: 10)")
    ap.add_argument("--out", type=Path, default=Path("Options.md"), help="Output file (default: Options.md; pass - for stdout)")
    args = ap.parse_args()

    solver_dir = args.solver_dir or default_solver_dir()
    wanted = set(args.solvers.split(",")) if args.solvers else None
    instances_by_family = discover_solver_instances(solver_dir, wanted)

    if not instances_by_family:
        print(f"No solvers found in {solver_dir}", file=sys.stderr)
        return 1

    rows = ROWS
    if args.groups:
        wanted_groups = set(args.groups.split(","))
        unknown = wanted_groups - set(GROUP_ORDER)
        if unknown:
            print(f"Unknown group(s): {', '.join(sorted(unknown))}", file=sys.stderr)
            return 1
        rows = [r for r in ROWS if r.group in wanted_groups]

    family_order = [n for n in SOLVER_FAMILIES if n in instances_by_family]
    all_instances = [
        (family, version, path, is_jar)
        for family in family_order
        for version, path, is_jar in instances_by_family[family]
    ]
    print(f"Solver directory: {solver_dir}", file=sys.stderr)
    print(f"Testing: {', '.join(f'{f} {v}' for f, v, _p, _j in all_instances)}", file=sys.stderr)
    print(f"Rows: {len(rows)}", file=sys.stderr)

    results: dict[tuple[tuple[str, str], str], Result] = {}
    with tempfile.TemporaryDirectory(prefix="smt-options-") as workdir:
        workdir_path = Path(workdir)
        total = len(all_instances) * len(rows)
        done = 0
        for family, version, path, is_jar in all_instances:
            for row in rows:
                res = run_row(family, path, is_jar, row, args.timeout, workdir_path)
                results[((family, version), row.name)] = res
                done += 1
                if done % 10 == 0 or done == total:
                    print(f"  {done}/{total}", file=sys.stderr)

    columns = [
        {"family": family, "versions": g["versions"]}
        for family in family_order
        for g in group_family_columns(family, instances_by_family[family], rows, results)
    ]

    md = render_markdown(columns, results)
    if str(args.out) == "-":
        print(md)
    else:
        args.out.write_text(md)
        print(f"Wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
