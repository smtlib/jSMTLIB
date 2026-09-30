#!/usr/bin/env python3
"""Combine the per-platform JSON produced by `logics-report.py --json` into one
report covering every solver on every platform, and check the results for
cross-platform consistency.

Each platform's run only sees the solver binaries shipped for that platform, so
no single run covers everything: alt-ergo is Linux/macOS-arm64 only, Simplify is
Linux/Windows only, and several z3 versions exist on some platforms but not
others. Combining the runs gives the whole picture.

The consistency check asks one question: for a given *solver version* and a given
logic name, did every platform that has that binary reach the same verdict? A
disagreement means either a genuinely platform-specific solver build or a flaky
probe (usually a timeout), and either way it is worth knowing about -- the
per-platform tables would each look perfectly self-consistent.

Usage:
  python3 combine-logics-reports.py RESULT.json [RESULT.json ...]
      [--out FILE] [--fail-on-inconsistency]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

GRADE_SYMBOL = {"Y": "✅", "P": "⚠️", "N": "❌"}
GRADE_WORD = {"Y": "accepted", "P": "ambiguous/timeout", "N": "rejected"}

# Same ordering the single-platform report uses.
GROUP_ORDER = ["Baseline", "Official", "Unofficial", "Control"]


def load(paths: list[Path]) -> list[dict]:
    out = []
    for p in paths:
        try:
            out.append(json.loads(p.read_text(encoding="utf-8")))
        except (OSError, ValueError) as e:
            sys.exit(f"error: cannot read {p}: {e}")
    if not out:
        sys.exit("error: no input files")
    return out


def row_order(reports: list[dict]) -> list[tuple[str, str]]:
    """Union of all platforms' rows as (group, name), in the canonical order.
    Taken as a union rather than from one report so a platform that somehow saw
    a different logic set cannot silently drop rows."""
    seen: dict[str, str] = {}
    for r in reports:
        for row in r["rows"]:
            seen.setdefault(row["name"], row["group"])
    def key(item):
        name, group = item
        gi = GROUP_ORDER.index(group) if group in GROUP_ORDER else len(GROUP_ORDER)
        return (gi, name)
    return [(g, n) for n, g in sorted(seen.items(), key=key)]


def solver_order(reports: list[dict]) -> list[str]:
    """Union of every solver version seen anywhere, family-grouped and
    version-sorted."""
    names = {s for r in reports for s in r["results"]}

    def key(s: str):
        family, _, version = s.partition(" ")
        return (family, [int(x) for x in version.replace("-", ".").split(".") if x.isdigit()])

    return sorted(names, key=key)


def find_inconsistencies(reports: list[dict]) -> list[dict]:
    """Every (solver version, logic) where platforms that both have the binary
    disagree on the verdict."""
    bad = []
    solvers = solver_order(reports)
    rows = row_order(reports)
    for solver in solvers:
        for _group, logic in rows:
            by_grade: dict[str, list[str]] = {}
            for r in reports:
                cell = r["results"].get(solver, {}).get(logic)
                if cell is None:
                    continue           # this platform doesn't ship this binary
                by_grade.setdefault(cell["grade"], []).append(r["platform"])
            if len(by_grade) > 1:
                bad.append({"solver": solver, "logic": logic, "by_grade": by_grade})
    return bad


def render(reports: list[dict], bad: list[dict]) -> str:
    platforms = [r["platform"] for r in reports]
    rows = row_order(reports)
    solvers = solver_order(reports)

    L: list[str] = []
    L.append("# SMT solver logic-name support, all platforms")
    L.append("")
    L.append("Combined from `logics-report.py --json` runs on: "
             + ", ".join(f"`{p}`" for p in platforms) + ".")
    L.append("")
    L.append("Each platform only ships some of the solver binaries, so a cell is blank "
             "(`·`) where that platform has no such binary -- which is different from "
             "the solver rejecting the logic (`❌`).")
    L.append("")

    # --- consistency -------------------------------------------------------
    L.append("## Cross-platform consistency")
    L.append("")
    if not bad:
        L.append("✅ No disagreements: every solver version that exists on more than one "
                 "platform returned the same verdict for every logic name.")
    else:
        L.append(f"⚠️ **{len(bad)} disagreement(s)** -- the same solver version reached "
                 "different verdicts on different platforms. Each is either a genuinely "
                 "platform-specific build difference or a flaky probe (most often a "
                 "timeout, which grades as ambiguous).")
        L.append("")
        L.append("| Solver | Logic | Verdicts by platform |")
        L.append("|:---|:---|:---|")
        for b in bad:
            parts = [f"{GRADE_SYMBOL[g]} {GRADE_WORD[g]}: {', '.join(sorted(ps))}"
                     for g, ps in sorted(b["by_grade"].items())]
            L.append(f"| `{b['solver']}` | `{b['logic']}` | " + " · ".join(parts) + " |")
    L.append("")

    # --- coverage ----------------------------------------------------------
    L.append("## Solver availability")
    L.append("")
    L.append("| Solver | " + " | ".join(platforms) + " |")
    L.append("|:---|" + ":---:|" * len(platforms))
    for s in solvers:
        cells = ["✅" if s in r["results"] else "" for r in reports]
        L.append(f"| `{s}` | " + " | ".join(cells) + " |")
    L.append("")

    # --- the combined table ------------------------------------------------
    L.append("## Logic acceptance")
    L.append("")
    L.append("Where a solver version exists on several platforms and they agree, the "
             "shared verdict is shown. A disagreement is shown as `‼` and listed above.")
    L.append("")
    L.append("| Group | Logic | " + " | ".join(f"`{s}`" for s in solvers) + " |")
    L.append("|:---|:---|" + ":---:|" * len(solvers))
    prev_group = None
    for group, logic in rows:
        label = group if group != prev_group else ""
        prev_group = group
        cells = []
        for s in solvers:
            grades = {r["results"][s][logic]["grade"]
                      for r in reports
                      if s in r["results"] and logic in r["results"][s]}
            if not grades:
                cells.append("·")
            elif len(grades) == 1:
                cells.append(GRADE_SYMBOL[grades.pop()])
            else:
                cells.append("‼")
        L.append(f"| {label} | `{logic}` | " + " | ".join(cells) + " |")
    L.append("")
    L.append("*Generated by `SMTTests/reports/combine-logics-reports.py`.*")
    return "\n".join(L) + "\n"


def main() -> int:
    # Windows consoles default to a legacy code page (cp1252 on the CI runners),
    # which cannot encode the report's grade symbols. Writing files is handled by
    # explicit encoding= arguments; this covers --out - and the progress output.
    for _stream in (sys.stdout, sys.stderr):
        try:
            _stream.reconfigure(encoding="utf-8")
        except (AttributeError, OSError):
            pass

    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="+", type=Path, help="per-platform JSON files")
    ap.add_argument("--out", type=Path, default=Path("Logics-all-platforms.md"),
                    help="output file (default: Logics-all-platforms.md; - for stdout)")
    ap.add_argument("--fail-on-inconsistency", action="store_true",
                    help="exit non-zero if any cross-platform disagreement is found")
    args = ap.parse_args()

    reports = load(args.inputs)
    reports.sort(key=lambda r: r["platform"])
    bad = find_inconsistencies(reports)
    text = render(reports, bad)

    if str(args.out) == "-":
        print(text)
    else:
        args.out.write_text(text, encoding="utf-8")
        print(f"Wrote {args.out}", file=sys.stderr)

    print(f"Platforms: {len(reports)}; solver versions: {len(solver_order(reports))}; "
          f"disagreements: {len(bad)}", file=sys.stderr)
    for b in bad:
        print(f"  INCONSISTENT {b['solver']} / {b['logic']}: "
              + "; ".join(f"{g}={','.join(sorted(ps))}" for g, ps in sorted(b["by_grade"].items())),
              file=sys.stderr)

    return 1 if (bad and args.fail_on_inconsistency) else 0


if __name__ == "__main__":
    sys.exit(main())
