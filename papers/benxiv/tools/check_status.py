#!/usr/bin/env python3
"""Audit every ``verified`` citation in the companion against the Lean tree.

A document that mixes machine-checked and hand-written results is only
honest if the machine-checked claims are actually checkable.  This tool
makes the citations mechanically inspectable: it harvests every
``\\Sverified{Decl}`` marker from the LaTeX sources, confirms that ``Decl``
exists in the Lean source tree, rejects executable proof-hole tokens, and
emits the appendix ledger table.

This is deliberately a *citation audit*, not a proof checker.  It neither
compiles Lean modules nor decides whether the English theorem has the same
meaning as the cited declaration.  Those are separate build and review gates;
claiming otherwise would make this tool part of the status drift it is meant to
prevent.

Exit status is nonzero if any claim fails, so the document cannot silently
drift away from the development it cites.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

MARKER = re.compile(
    r"\\S(verified|prose|conditional|open|refuted|source)"
    r"(?:\{((?:[^{}]|\{[^{}]*\})*)\})?"
)
RESULT_ENVIRONMENTS = {
    "theorem", "lemma", "corollary", "proposition", "remark", "definition"
}
ENV_TOKEN = re.compile(
    r"\\(begin|end)\{(theorem|lemma|corollary|proposition|remark|definition)\}"
)
HOLE = re.compile(r"(?<![A-Za-z_])(sorry|admit|native_decide)(?![A-Za-z_])")

ACCEPTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def _result_spans(text: str) -> list[tuple[int, int, str]]:
    """Return the spans of theorem-like environments, including definitions."""
    stack: list[tuple[str, int]] = []
    spans: list[tuple[int, int, str]] = []
    for token in ENV_TOKEN.finditer(text):
        action, kind = token.groups()
        if action == "begin":
            stack.append((kind, token.start()))
            continue
        for i in range(len(stack) - 1, -1, -1):
            if stack[i][0] == kind:
                _, start = stack.pop(i)
                spans.append((start, token.end(), kind))
                break
    return spans


def _kind_at(position: int, spans: list[tuple[int, int, str]]) -> str:
    containing = [span for span in spans if span[0] <= position <= span[1]]
    if not containing:
        return "statement"
    return min(containing, key=lambda span: span[1] - span[0])[2]


def harvest(tex_paths: list[pathlib.Path]) -> list[dict]:
    """Collect every status marker with the result it qualifies."""
    entries = []
    for path in tex_paths:
        text = path.read_text(encoding="utf-8")
        spans = _result_spans(text)
        for match in MARKER.finditer(text):
            before = text[: match.start()]
            entries.append(
                {
                    "file": path.name,
                    "line": before.count("\n") + 1,
                    "status": match.group(1),
                    "payload": (match.group(2) or "").strip(),
                    "kind": _kind_at(match.start(), spans),
                }
            )
    return entries


def lean_code_only(source: str) -> str:
    """Mask Lean comments and strings while preserving positions and newlines."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                out.extend("  ")
                block_depth += 1
                i += 2
            elif source.startswith("-/", i):
                out.extend("  ")
                block_depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            char = source[i]
            out.append("\n" if char == "\n" else " ")
            i += 1
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if source.startswith("/-", i):
            out.extend("  ")
            block_depth = 1
            i += 2
            continue
        if source[i] == '"':
            out.append(" ")
            in_string = True
            i += 1
            continue
        out.append(source[i])
        i += 1
    return "".join(out)


def declaration_module(decl: str, lean_root: pathlib.Path) -> pathlib.Path | None:
    """Map a fully qualified declaration to the file that should define it."""
    parts = decl.split(".")
    for cut in range(len(parts) - 1, 0, -1):
        candidate = lean_root.joinpath(*parts[:cut]).with_suffix(".lean")
        if candidate.is_file():
            return candidate
    return None


def check_verified(entry: dict, lean_root: pathlib.Path) -> tuple[bool, str]:
    decl = entry["payload"]
    if not decl:
        return False, "no declaration named"
    module = declaration_module(decl, lean_root)
    if module is None:
        return False, f"no module found for {decl}"
    source = lean_code_only(module.read_text(encoding="utf-8"))
    short = decl.split(".")[-1]
    if not re.search(rf"(?<![A-Za-z_.]){re.escape(short)}(?![A-Za-z_])", source):
        return False, f"{short} not found in {module.name}"
    holes = HOLE.findall(source)
    if holes:
        return False, f"{module.name} contains {sorted(set(holes))}"
    return True, module.name


def _display(payload: str) -> str:
    """Render a payload as inert text.

    Payloads may carry LaTeX (a `\\ref` naming a dependency, say).  The ledger
    shows them, it does not re-execute them, so commands and braces are
    stripped rather than passed through -- otherwise a nested brace ends a
    `\\texttt` early and the document fails to build.
    """
    flat = re.sub(r"\\[a-zA-Z]+", "", payload)
    flat = flat.replace("{", "").replace("}", "").replace("~", " ")
    return flat.replace("_", r"\_").strip()


def emit_ledger(entries: list[dict], out: pathlib.Path) -> None:
    order = {"verified": 0, "prose": 1, "conditional": 2, "open": 3,
             "refuted": 4, "source": 5}
    rows = sorted(entries, key=lambda e: (order[e["status"]], e["file"], e["line"]))
    lines = [
        "% Generated by tools/check_status.py -- do not edit by hand.",
        r"\begin{center}",
        r"\small",
        r"\begin{tabular}{@{}llp{0.52\textwidth}@{}}",
        r"\toprule",
        r"Result & Status & Machine-checkable claim \\",
        r"\midrule",
    ]
    for row in rows:
        payload = _display(row["payload"]) or "--"
        where = f"{row['kind']} ({row['file']}:{row['line']})"
        lines.append(
            rf"{where} & \textsc{{{row['status']}}} & \texttt{{\scriptsize {payload}}} \\"
        )
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{center}", ""]
    out.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex", nargs="+", required=True)
    parser.add_argument("--lean-root", required=True)
    parser.add_argument("--ledger", default=None)
    args = parser.parse_args()

    tex_paths = [pathlib.Path(p) for p in args.tex]
    lean_root = pathlib.Path(args.lean_root)
    entries = harvest(tex_paths)

    failures = []
    for entry in entries:
        if entry["status"] != "verified":
            continue
        ok, detail = check_verified(entry, lean_root)
        status = "OK  " if ok else "FAIL"
        print(f"{status} {entry['file']}:{entry['line']}  {detail}")
        if not ok:
            failures.append(entry)

    counts = {}
    for entry in entries:
        counts[entry["status"]] = counts.get(entry["status"], 0) + 1
    print("\nledger:", ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))

    if args.ledger:
        emit_ledger(entries, pathlib.Path(args.ledger))
        print("wrote", args.ledger)

    if failures:
        print(f"\n{len(failures)} verified-claim(s) FAILED", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
