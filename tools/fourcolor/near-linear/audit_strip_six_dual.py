#!/usr/bin/env python3
"""Replay the exact dual of the fixed-order obstruction from its sphere fixture."""

import ast
import hashlib
import json
from pathlib import Path
import re


def main():
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    fixture = here / "strip-six-order-example.json"
    source = repo / "lean/fourcolor-classical/MettapediaFourColor/StripSixDualExample.lean"
    data = json.loads(fixture.read_text())
    rows, faces = data["whole_rows"], data["whole_faces"]
    assert len(rows) == 41 and len(faces) == 78
    primal = {(u, v) for u, row in enumerate(rows) for v in row}
    face_of = {}
    for f, triangle in enumerate(faces):
        assert len(set(triangle)) == 3
        for i in range(3):
            u, v, w = (triangle[(i + j) % 3] for j in range(3))
            assert rows[v][(rows[v].index(u) + 1) % len(rows[v])] == w
            assert (u, v) not in face_of
            face_of[u, v] = f
    assert set(face_of) == primal and len(primal) == 234
    dual = [[face_of[t[(i + 1) % 3], t[i]] for i in range(3)] for t in faces]
    ids = [[face_of[u, v] for v in row] for u, row in enumerate(rows)]
    text = source.read_text()
    for name, expected in [("star", dual), ("triangle", faces), ("faceIds", ids)]:
        match = re.search(r"def " + name + r"\b[^\n]*:= !(\[.*?\])\n", text, re.S)
        assert match, name
        assert ast.literal_eval(match[1]) == expected, name
    forward = lambda u, v: (face_of[u, v], face_of[v, u])
    for u, row in enumerate(dual):
        assert len(set(row)) == 3 and u not in row
        for i, v in enumerate(row):
            assert u in dual[v]
            a, b = faces[u][i], faces[u][(i + 1) % 3]
            assert forward(a, b) == (u, v)
    for u, v in primal:
        f, g = forward(u, v)
        assert forward(v, u) == (g, f)
        assert (f, dual[f][(dual[f].index(g) + 1) % 3]) == forward(
            v, rows[v][(rows[v].index(u) + 1) % len(rows[v])])
        assert (g, dual[g][(dual[g].index(f) + 1) % 3]) == forward(
            u, rows[u][(rows[u].index(v) + 1) % len(rows[u])])
    root = (22, 0)
    assert len(rows[root[0]]) == 5
    neighbours = [rows[22][(rows[22].index(0) + i) % 5] for i in (1, 2, 3)]
    assert neighbours == [17, 25, 13] and all(len(rows[v]) == 5 for v in neighbours)
    report = {
        "classification": "EXACT_DUAL_PROGRAM_REPLAY",
        "fixture_sha256": hashlib.sha256(fixture.read_bytes()).hexdigest(),
        "lean_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "primal_vertices": 41,
        "dual_vertices": 78,
        "directed_edges": 234,
        "root": list(root),
        "consecutive_degree_five_neighbours": neighbours,
        "checked": ["all directed edges in both directions", "edge reversal",
                    "vertex and face permutations", "complete ordered degree pattern"],
        "limit": "The Lean consumer excludes dual vertex minimality. Universal alternative-piece supply and unconditional strict reduction of this fixture are not claimed.",
    }
    (here / "strip-six-dual-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
