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

# ASCII only, deliberately. This report is a CI artifact -- read in run
# summaries, terminals and logs, where the encoding is least predictable --
# and the first all-platform run died on exactly that (cp1252 on the Windows
# runner could not encode the grade emoji). The per-platform Markdown keeps
# its emoji: that one is published to GitHub Pages, where they render.
GRADE_SYMBOL = {"Y": "Y", "P": "?", "N": "n"}
NOT_PRESENT = "-"      # platform does not ship this binary
DISAGREEMENT = "!"     # platforms disagree; listed in the consistency section
GRADE_WORD = {"Y": "accepted", "P": "ambiguous/timeout", "N": "rejected"}

# Same ordering the single-platform report uses.
GROUP_ORDER = ["Baseline", "Official", "Unofficial", "Control"]


UNUSABLE = "x"          # binary present but unusable on this platform


ACCEPTS_ANYTHING = "A"  # accepted, but this solver accepts any string


def nonvalidating_solvers(reports: list[dict], rows: list[tuple[str, str]],
                          dead: set[tuple[str, str]]) -> set[str]:
    """Solvers that accept the deliberately invalid control logic, and so do not
    validate the set-logic argument at all. An acceptance from one of these means
    "accepted some string", not "recognized this logic", so it is marked A rather
    than Y. Currently bitwuzla 0.9.1 and z3 before 4.5.0."""
    control = [n for g, n in rows if g == "Control"]
    out = set()
    for solver in solver_order(reports):
        grades = set()
        for r in reports:
            if (r["platform"], solver) in dead:
                continue
            for c in control:
                cell = r["results"].get(solver, {}).get(c)
                if cell:
                    grades.add(cell["grade"])
        if grades == {"Y"}:
            out.add(solver)
    return out


def unusable_pairs(reports: list[dict]) -> set[tuple[str, str]]:
    """(platform, solver) pairs where the binary is present but produced no
    usable verdict on any row -- it timed out (and was then abandoned by
    logics-report.py). That is one fact about the binary, not 45 logic
    verdicts, and letting it through as a per-row disagreement is what buried
    the genuine findings in the first all-platform run."""
    bad = set()
    for r in reports:
        for solver, rows in r["results"].items():
            if rows and all(c["grade"] == "P" for c in rows.values()):
                bad.add((r["platform"], solver))
    return bad


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
    dead = unusable_pairs(reports)
    for solver in solvers:
        for _group, logic in rows:
            by_grade: dict[str, list[str]] = {}
            for r in reports:
                cell = r["results"].get(solver, {}).get(logic)
                if cell is None:
                    continue           # this platform doesn't ship this binary
                if (r["platform"], solver) in dead:
                    continue           # reported once, under "Unusable binaries"
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
    L.append("Each platform only ships some of the solver binaries, so `-` (no such "
             "binary here) is a different answer from `n` (the solver rejected the "
             "logic).")
    L.append("")
    L.append("| | meaning |")
    L.append("|:---:|:---|")
    L.append("| `Y` | accepted -- the solver answered `success` |")
    L.append("| `A` | accepted, but this solver accepts any string, valid logic or not |")
    L.append("| `n` | rejected -- `unsupported`, an error, or no response |")
    L.append("| `?` | ambiguous response, or the probe timed out |")
    L.append("| `-` | this platform ships no such solver binary |")
    L.append("| `!` | platforms disagree; see the consistency section |")
    L.append("| `x` | binary present but unusable on every platform that has it |")
    L.append("")

    # --- consistency -------------------------------------------------------
    L.append("## Cross-platform consistency")
    L.append("")
    if not bad:
        L.append("No disagreements: every solver version that exists on more than one "
                 "platform returned the same verdict for every logic name.")
    else:
        L.append(f"**{len(bad)} disagreement(s)** -- the same solver version reached "
                 "different verdicts on different platforms. Each is either a genuinely "
                 "platform-specific build difference or a flaky probe (most often a "
                 "timeout, which grades as ambiguous).")
        L.append("")
        L.append("| Solver | Logic | Verdicts by platform |")
        L.append("|:---|:---|:---|")
        for b in bad:
            parts = [f"{GRADE_SYMBOL[g]} {GRADE_WORD[g]}: {', '.join(sorted(ps))}"
                     for g, ps in sorted(b["by_grade"].items())]
            L.append(f"| `{b['solver']}` | `{b['logic']}` | " + "; ".join(parts) + " |")
    L.append("")

    # --- unusable binaries -------------------------------------------------
    dead = unusable_pairs(reports)
    if dead:
        L.append("## Unusable binaries")
        L.append("")
        L.append("These binaries are present but produced no usable verdict on any row: "
                 "every probe timed out. That is one fact about the binary on that "
                 "platform, not a per-logic result, so these are excluded from the "
                 "consistency check above and shown as `x` below.")
        L.append("")
        L.append("| Solver | Platform |")
        L.append("|:---|:---|")
        for solver, plat in sorted((s2, p2) for p2, s2 in dead):
            L.append(f"| `{solver}` | {plat} |")
        L.append("")

    # --- coverage ----------------------------------------------------------
    L.append("## Solver availability")
    L.append("")
    L.append("| Solver | " + " | ".join(platforms) + " |")
    L.append("|:---|" + ":---:|" * len(platforms))
    for s in solvers:
        cells = ["Y" if s in r["results"] else NOT_PRESENT for r in reports]
        L.append(f"| `{s}` | " + " | ".join(cells) + " |")
    L.append("")

    # --- the combined table ------------------------------------------------
    L.append("## Logic acceptance")
    L.append("")
    L.append("Where a solver version exists on several platforms and they agree, the "
             "shared verdict is shown. A disagreement is shown as `!` and listed above.")
    L.append("")
    loose = nonvalidating_solvers(reports, rows, dead)
    if loose:
        L.append("`A` marks " + ", ".join(f"`{x}`" for x in sorted(loose)) +
                 ": these accept the invalid control logic too, so they do not validate "
                 "the `set-logic` argument at all, and an acceptance says nothing about "
                 "the specific logic named.")
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
                      if s in r["results"] and logic in r["results"][s]
                      and (r["platform"], s) not in dead}
            if not grades and any(s in r["results"] for r in reports):
                cells.append(UNUSABLE)
                continue
            if not grades:
                cells.append(NOT_PRESENT)
            elif len(grades) == 1:
                g = grades.pop()
                cells.append(ACCEPTS_ANYTHING
                             if g == "Y" and s in loose
                             else GRADE_SYMBOL[g])
            else:
                cells.append(DISAGREEMENT)
        L.append(f"| {label} | `{logic}` | " + " | ".join(cells) + " |")
    L.append("")
    L.append("*Generated by `SMTTests/reports/combine-logics-reports.py`.*")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------
# LaTeX rendering (for the tutorial's "SMT-LIB Logics supported by solvers"
# appendix). Letters rather than symbols: there are six distinct states here,
# which is more than bullets can carry legibly.
# ---------------------------------------------------------------------------

LATEX_SPECIAL = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
                 "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
                 "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}


def tex_escape(t: str) -> str:
    return "".join(LATEX_SPECIAL.get(c, c) for c in t if ord(c) < 128)

def merge_columns(reports, rows, dead, loose):
    """Collapse adjacent same-family versions whose consolidated verdicts are
    identical into one column, exactly as the single-platform report does. 18
    solver versions become a handful of columns, which is the difference
    between a table that fits the page and one that does not."""
    cols = []
    for solver in solver_order(reports):
        vec = tuple(cell_for(reports, dead, loose, solver, l) for _g, l in rows)
        fam = solver.split(" ")[0]
        if cols and cols[-1]["family"] == fam and cols[-1]["vec"] == vec:
            cols[-1]["versions"].append(solver.split(" ", 1)[1])
        else:
            cols.append({"family": fam, "versions": [solver.split(" ", 1)[1]],
                         "vec": vec})
    return cols


def cell_for(reports, dead, loose, solver, logic) -> str:
    grades = {r["results"][solver][logic]["grade"] for r in reports
              if solver in r["results"] and logic in r["results"][solver]
              and (r["platform"], solver) not in dead}
    if not grades:
        return UNUSABLE if any(solver in r["results"] for r in reports) else NOT_PRESENT
    if len(grades) == 1:
        g = grades.pop()
        return ACCEPTS_ANYTHING if g == "Y" and solver in loose else GRADE_SYMBOL[g]
    return DISAGREEMENT


def col_label(c) -> str:
    v = c["versions"]
    if len(v) == 1:
        return f"{c['family']} {v[0]}"
    if len(v) == 2:
        return f"{c['family']} {v[0]}, {v[1]}"
    return f"{c['family']} {v[0]}-{v[-1]}"


def render_latex(reports: list[dict], bad: list[dict]) -> str:
    """Upright, not sideways: with adjacent identical versions merged the table is
    tall and narrow, and rotating it pushes the ~45 rows off the page (measured --
    the unmerged 18-column version overflowed by 47pt even in landscape)."""
    platforms = [r["platform"] for r in reports]
    rows = row_order(reports)
    dead = unusable_pairs(reports)
    loose = nonvalidating_solvers(reports, rows, dead)
    cols = merge_columns(reports, rows, dead, loose)

    head = ["{\\bf Group}", "{\\bf Logic}"]
    for c in cols:
        lab = tex_escape(col_label(c))
        fam, _, rest = lab.partition(" ")
        head.append("\\begin{tabular}{@{}c@{}}%s\\\\%s\\end{tabular}" % (fam, rest))

    body = ["\\hline", " & ".join(head) + " \\\\"]
    for group in GROUP_ORDER:
        grows = [(g, l) for g, l in rows if g == group]
        if not grows:
            continue
        body.append("\\hline\\hline")
        first = True
        for _g, logic in grows:
            cells = [group if first else "", "{\\tt %s}" % tex_escape(logic)]
            first = False
            ri = [l for _gg, l in rows].index(logic)
            cells += [c["vec"][ri] for c in cols]
            body.append(" & ".join(cells) + " \\\\")

    out = ["%% Generated by SMTTests/reports/combine-logics-reports.py --tex -- do not edit.",
           "", "\\begin{table}[p]", "\\centering", "\\scriptsize",
           "\\renewcommand{\\arraystretch}{0.9}",
           "\\begin{tabular}{|l|l|" + "c|" * len(cols) + "}"]
    out += body + ["\\hline", "\\end{tabular}"]
    out.append("\\caption{Logic names accepted by each solver, combined across "
               + tex_escape(", ".join(platforms)) + ". {\\tt Y} accepted; {\\tt A} accepted "
               "by a solver that accepts any string at all, so it says nothing about the "
               "logic named; {\\tt n} rejected; {\\tt ?} ambiguous or timed out; "
               "{\\tt x} binary present but unusable; {\\tt -} no such binary; "
               "{\\tt !} platforms disagree. Versions of one solver that answered every "
               "row identically share a column.}")
    out.append("\\label{tab:supported-logics}")
    notes = []
    if loose:
        notes.append("Do not validate the set-logic argument (they accept the invalid "
                     "control logic too): " + tex_escape(", ".join(sorted(loose))) + ".")
    if dead:
        notes.append("Present but unusable, every probe timing out: "
                     + tex_escape("; ".join(f"{s2} on {p2}" for p2, s2 in sorted(dead))) + ".")
    for b in bad:
        notes.append(tex_escape("%s / %s: " % (b["solver"], b["logic"]) +
                     "; ".join(f"{GRADE_WORD[g]} on {', '.join(sorted(ps))}"
                               for g, ps in sorted(b["by_grade"].items()))) + ".")
    if notes:
        out.append("\\begin{flushleft}\\scriptsize")
        out += ["%s\\par" % n for n in notes]
        out.append("\\end{flushleft}")
    out += ["\\end{table}", ""]
    return "\n".join(out)


HTML_HEAD = """<title>jSMTLIB: %(title)s</title>
<meta name="keywords" content="SMT solvers, SMT-LIB logics, set-logic">
<meta name="description" content="%(desc)s">
<link href="book.css" rel="STYLESHEET" type="text/css" />

<div id="Breadcrumb">
   <a href="/">Home</a> /
   <a href="index.html">jSMTLIB project and SMT-LIB resources</a> /
   <strong>%(title)s</strong>
</div>

<h1>%(title)s</h1>
"""

LEGEND = [("Y", "accepted -- the solver answered <tt>success</tt>"),
          ("A", "accepted, but this solver accepts any string, valid logic or not"),
          ("n", "rejected -- <tt>unsupported</tt>, an error, or no response"),
          ("?", "ambiguous response, or the probe timed out"),
          ("-", "this platform ships no such solver binary"),
          ("x", "binary present but unusable on every platform that has it"),
          ("!", "platforms disagree; see the consistency section")]


def render_html(reports: list[dict], bad: list[dict]) -> str:
    """Plain HTML, not Markdown: GitHub Pages runs Jekyll, and Jekyll leaves a .md
    file without YAML front matter untouched, so it is served as raw text."""
    platforms = [r["platform"] for r in reports]
    rows = row_order(reports)
    dead = unusable_pairs(reports)
    loose = nonvalidating_solvers(reports, rows, dead)
    cols = merge_columns(reports, rows, dead, loose)

    L = [HTML_HEAD % {"title": "SMT-LIB logics accepted by each solver",
                      "desc": "Which SMT-LIB logic names each solver accepts, across platforms."}]
    L.append("<p>For every logic name jSMTLIB knows about, this records whether "
             "<tt>(set-logic L)</tt> gets a plain <tt>success</tt> response -- not whether the "
             "solver can actually do anything useful in that logic. Combined from runs on: "
             + ", ".join("<tt>%s</tt>" % p for p in platforms) + ".</p>")
    L.append("<p>Versions of one solver that answered every row identically share a column.</p>")
    L.append("<table>")
    L.append("<tr><th>&nbsp;</th><th>meaning</th></tr>")
    for sym, txt in LEGEND:
        L.append("<tr><td align=\"center\"><tt>%s</tt></td><td>%s</td></tr>" % (sym, txt))
    L.append("</table>")

    L.append("<h2>Cross-platform consistency</h2>")
    if not bad:
        L.append("<p>No disagreements: every solver version present on more than one "
                 "platform returned the same verdict for every logic name.</p>")
    else:
        L.append("<p><strong>%d disagreement(s)</strong> -- the same solver version reached "
                 "different verdicts on different platforms.</p>" % len(bad))
        L.append("<table><tr><th>Solver</th><th>Logic</th><th>Verdicts by platform</th></tr>")
        for b in bad:
            parts = "; ".join("%s on %s" % (GRADE_WORD[g], ", ".join(sorted(ps)))
                              for g, ps in sorted(b["by_grade"].items()))
            L.append("<tr><td><tt>%s</tt></td><td><tt>%s</tt></td><td>%s</td></tr>"
                     % (b["solver"], b["logic"], parts))
        L.append("</table>")

    if dead:
        L.append("<h2>Unusable binaries</h2>")
        L.append("<p>Present, but every probe timed out. That is one fact about the binary on "
                 "that platform, not a per-logic result, so these are excluded from the "
                 "consistency check and shown as <tt>x</tt> below.</p>")
        L.append("<table><tr><th>Solver</th><th>Platform</th></tr>")
        for solver, plat in sorted((s2, p2) for p2, s2 in dead):
            L.append("<tr><td><tt>%s</tt></td><td>%s</td></tr>" % (solver, plat))
        L.append("</table>")

    L.append("<h2>Logic acceptance</h2>")
    if loose:
        L.append("<p><tt>A</tt> marks " + ", ".join("<tt>%s</tt>" % x for x in sorted(loose)) +
                 ": these accept the invalid control logic too, so they do not validate the "
                 "<tt>set-logic</tt> argument at all.</p>")
    L.append("<table>")
    L.append("<tr><th>Group</th><th>Logic</th>" +
             "".join("<th>%s</th>" % col_label(c).replace(" ", "<br/>", 1) for c in cols) +
             "</tr>")
    prev = None
    names = [l for _g, l in rows]
    for g, logic in rows:
        lab = g if g != prev else "&nbsp;"
        prev = g
        ri = names.index(logic)
        cells = "".join("<td align=\"center\"><tt>%s</tt></td>" % c["vec"][ri] for c in cols)
        L.append("<tr><td>%s</td><td><tt>%s</tt></td>%s</tr>" % (lab, logic, cells))
    L.append("</table>")
    L.append("<p><em>Generated by <tt>SMTTests/reports/combine-logics-reports.py</tt> in the "
             "jSMTLIB repository.</em></p>")
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
    ap.add_argument("--out", type=Path, default=None,
                    help="write the Markdown report here ('-' for stdout). Used for the CI run "
                         "summary; the published site takes --html instead, since GitHub Pages "
                         "serves a .md without YAML front matter as raw text.")
    ap.add_argument("--tex", type=Path, default=None,
                    help="also write a LaTeX table for the tutorial appendix")
    ap.add_argument("--html", type=Path, default=None,
                    help="also write a standalone HTML page for GitHub Pages")
    ap.add_argument("--fail-on-inconsistency", action="store_true",
                    help="exit non-zero if any cross-platform disagreement is found")
    args = ap.parse_args()

    if not (args.out or args.tex or args.html):
        ap.error("nothing to do: give at least one of --out, --tex, --html")

    reports = load(args.inputs)
    reports.sort(key=lambda r: r["platform"])
    bad = find_inconsistencies(reports)
    if args.out:
        text = render(reports, bad)
        if str(args.out) == "-":
            print(text)
        else:
            args.out.write_text(text, encoding="utf-8")
            print(f"Wrote {args.out}", file=sys.stderr)

    if args.html:
        args.html.write_text(render_html(reports, bad), encoding="utf-8")
        print(f"Wrote {args.html}", file=sys.stderr)

    if args.tex:
        args.tex.write_text(render_latex(reports, bad), encoding="utf-8")
        print(f"Wrote {args.tex}", file=sys.stderr)

    print(f"Platforms: {len(reports)}; solver versions: {len(solver_order(reports))}; "
          f"disagreements: {len(bad)}", file=sys.stderr)
    for b in bad:
        print(f"  INCONSISTENT {b['solver']} / {b['logic']}: "
              + "; ".join(f"{g}={','.join(sorted(ps))}" for g, ps in sorted(b["by_grade"].items())),
              file=sys.stderr)

    return 1 if (bad and args.fail_on_inconsistency) else 0


if __name__ == "__main__":
    sys.exit(main())
