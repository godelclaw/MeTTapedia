#!/usr/bin/env python3
"""Compare the pinned D3009 rows with the Lean source decoder input."""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    raw = (here / "D3009.conf").read_bytes()
    expected = "5453856a156bd63835ddac419ebbe276ac6ae81b0a11b909cf928bf0b1686a3f"
    digest = hashlib.sha256(raw).hexdigest()
    if digest != expected:
        raise SystemExit("Pinned source hash differs")
    lean = (root / "lean/fourcolor-classical/MettapediaFourColor/D3009Wheel.lean").read_text()
    literal = re.search(r'source := (".*?")\s+valid :=', lean, re.S)
    if literal is None:
        raise SystemExit("Missing Lean source literal")
    decoded = json.loads(re.sub(r"\\\n\s*", "", literal.group(1)))
    rows = lambda s: [list(map(int, line.split())) for line in s.splitlines() if line.strip()]
    source = rows(raw.decode("ascii"))
    if rows(decoded) != source:
        raise SystemExit("Lean rows differ from the pinned source")
    size, ports = source[0]
    edges = {tuple(sorted((i, i % ports + 1))) for i in range(1, ports + 1)}
    for v, degree, *neighbors in source[1:]:
        if degree != len(neighbors) or len(set(neighbors)) != degree:
            raise SystemExit("Invalid internal row")
        edges.update(tuple(sorted((v, w))) for w in neighbors)
    triangles = sum(all(tuple(sorted(pair)) in edges for pair in itertools.combinations(t, 2))
                    for t in itertools.combinations(range(1, size + 1), 3))
    report = dict(
        source="near-linear-4ct/reducible-configurations/D3009.conf",
        revision="c2ce7a96e35256201526e2abb51a39d04a588b53",
        sha256=digest, lean_rows_equal=True, vertices=size, boundary_ports=ports,
        core_vertices=size - ports, edges=len(edges), triangles=triangles,
        scope="Source provenance and finite graph inventory. General occurrence is proved in Lean; no colouring repair is certified by this script.",
    )
    result = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
