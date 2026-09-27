#!/usr/bin/env python3
"""Inventory the RSST data and compare Gonthier/Lean construction programs.

This is a source and geometry consistency check, not a reducibility proof.
Inputs are supplied explicitly; the program downloads and executes nothing.
The RSST record format is documented at
https://thomas.math.gatech.edu/FC/ftpinfo.html .
"""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_configurations(text):
    """Check the literal cyclic adjacency data of every free completion."""
    tokens = iter(text.split())
    records = []
    for name in tokens:
        n, ring, color_count, residual_count = (int(next(tokens)) for _ in range(4))
        require(3 <= ring <= n, f"{name}: invalid ring size")
        contract_size = int(next(tokens))
        require(0 <= contract_size, f"{name}: negative contract size")
        contract = [(int(next(tokens)), int(next(tokens))) for _ in range(contract_size)]
        adjacency = {}
        for expected in range(1, n + 1):
            vertex, degree = int(next(tokens)), int(next(tokens))
            require(vertex == expected and degree >= 2, f"{name}: malformed adjacency row")
            neighbours = [int(next(tokens)) for _ in range(degree)]
            require(len(set(neighbours)) == degree and vertex not in neighbours,
                    f"{name}: loops or repeated neighbours")
            require(all(1 <= w <= n for w in neighbours), f"{name}: invalid endpoint")
            adjacency[vertex] = neighbours
        coordinates = [int(next(tokens)) for _ in range(n)]
        require(all(0 <= v < 1024**2 for v in coordinates), f"{name}: invalid coordinates")
        require(all(v in adjacency[w] for v, ns in adjacency.items() for w in ns),
                f"{name}: asymmetric adjacency")
        require(all(v % ring + 1 in adjacency[v] for v in range(1, ring + 1)),
                f"{name}: missing ring edge")
        require(all(v in adjacency and w in adjacency[v] for v, w in contract),
                f"{name}: contract refers to a missing edge")
        darts = {(v, w) for v, ns in adjacency.items() for w in ns}
        edge_count = len(darts) // 2
        faces = []
        while darts:
            start = min(darts)
            dart, cycle = start, []
            while dart not in cycle:
                require(dart in darts, f"{name}: face traversal repeats another cycle")
                darts.remove(dart)
                cycle.append(dart)
                v, w = dart
                ns = adjacency[w]
                dart = w, ns[(ns.index(v) + 1) % len(ns)]
            require(dart == start, f"{name}: face traversal does not close")
            faces.append(cycle)
        # Connectivity is checked independently of the Euler equality.
        seen, pending = {1}, [1]
        while pending:
            for w in adjacency[pending.pop()]:
                if w not in seen:
                    seen.add(w)
                    pending.append(w)
        require(len(seen) == n, f"{name}: disconnected free completion")
        outer = [f for f in faces if len(f) == ring and
                 {v for v, _ in f} == set(range(1, ring + 1))]
        require(len(outer) == 1, f"{name}: outer face is not the specified ring")
        require(all(f == outer[0] or len(f) == 3 for f in faces),
                f"{name}: nontriangular inner face")
        require(n - edge_count + len(faces) == 2, f"{name}: nonspherical Euler count")
        require(edge_count == 3*n - ring - 3, f"{name}: wrong disk edge count")
        records.append({"ordinal": len(records) + 1, "name": name, "ring": ring,
                        "free_completion_vertices": n, "edges": edge_count,
                        "faces": len(faces), "source_C": color_count,
                        "source_Cprime": residual_count, "contraction_edges": contract_size})
    return records


def read_rules(text):
    """Count published rule labels separately from the oriented machine entries."""
    entries = []
    for block in re.split(r"\n\s*\n", text):
        lines = [line.strip() for line in block.splitlines()
                 if line.strip() and not line.lstrip().startswith("#")]
        if not lines:
            continue
        head = lines[0].split()
        require(int(head[0]) == len(entries) + 1, "nonsequential machine rule number")
        inverse = head[1:] == ["invert"]
        require((inverse and len(lines) == 1) or
                (not inverse and len(head) == 3 and len(lines) <= 2), "malformed rule")
        if not inverse:
            require(all(t.isdigit() for t in head), "nonnumeric rule bounds")
            if len(lines) == 2:
                tail = lines[1].split()
                require(len(tail) % 2 == 0 and all(t.isdigit() for t in tail),
                        "malformed local rule constraints")
        entries.append({"number": int(head[0]), "inverse": inverse})
    labels = list(map(int, re.findall(r"^# Rule (\d+)\s*$", text, re.MULTILINE)))
    require(labels == list(range(1, len(labels) + 1)), "nonsequential published rule labels")
    return {"published_rules": len(labels), "machine_entries": len(entries),
            "inverse_entries": sum(entry["inverse"] for entry in entries)}


def read_rocq_programs(text):
    records = []
    pattern = r"Definition cf(\d+)\s*:=\s*Config(\*?)\s+([^.]*)\."
    for match in re.finditer(pattern, text):
        number = int(match[1])
        require(number == len(records) + 1, "nonsequential Rocq configuration")
        tokens = match[3].split()
        contract = []
        while tokens and tokens[0].isdigit():
            contract.append(int(tokens.pop(0)))
        require(tokens and all(t in ("H", "Y") or t.isdigit() for t in tokens),
                f"cf{number:03}: unexpected program instruction")
        program = [("R", int(t)) if t.isdigit() else (t,) for t in tokens]
        records.append((bool(match[2]), contract, program))
    return records


def read_lean_programs(text):
    records = []
    pattern = r"def cf(\d+) : Config :=\s*⟨(true|false), \[([^\]]*)\], \[([^\]]*)\]⟩"
    for match in re.finditer(pattern, text):
        number = int(match[1])
        require(number == len(records) + 1, "nonsequential Lean configuration")
        contract = [int(x.strip()) for x in match[3].split(",") if x.strip()]
        program = []
        for token in match[4].split(","):
            token = token.strip()
            if re.fullmatch(r"\.R \d+", token):
                program.append(("R", int(token[3:])))
            else:
                require(token in (".H", ".Y"), f"cf{number:03}: unexpected Lean instruction")
                program.append((token[1:],))
        records.append((match[2] == "true", contract, program))
    return records


def inventory(conf_text, rules_text, rocq_text, lean_text):
    records = read_configurations(conf_text)
    rocq = read_rocq_programs(rocq_text)
    lean = read_lean_programs(lean_text)
    require(len(records) == len(rocq) == len(lean) == 633, "expected 633 configurations")
    require(rocq == lean, "Rocq and Lean construction data differ")
    for record, (_, _, prog) in zip(records, rocq):
        require(record["ring"] == 2 + sum(step == ("Y",) for step in prog),
                f"{record['name']}: ring size differs from construction program")
    histogram = lambda field: dict(sorted(Counter(r[field] for r in records).items()))
    return {
        "verification": "program-checked source consistency; no Lean reducibility claim",
        "configurations": len(records), "ring_histogram": histogram("ring"),
        "contraction_size_histogram": histogram("contraction_edges"),
        "source_zero_residual_count": sum(r["source_Cprime"] == 0 for r in records),
        "source_nonzero_residual_count": sum(r["source_Cprime"] != 0 for r in records),
        "rules": read_rules(rules_text),
        "rocq_lean_programs_equal": True,
        "rsst_program_ring_sizes_equal": True,
        "graph_checks": ["simple symmetric adjacency", "connected free completion",
                         "ordered outer ring", "triangular inner faces", "Euler count 2",
                         "contract edge references"],
        "not_checked": ["RSST versus program map isomorphism", "colour counts in headers",
                        "reducibility", "discharging validity", "unavoidability"],
        "records": records,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configurations", type=Path, required=True)
    parser.add_argument("--rules", type=Path, required=True)
    parser.add_argument("--rocq-programs", type=Path, required=True)
    parser.add_argument("--lean-programs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    paths = {k: v for k, v in vars(args).items() if k != "output"}
    data = {k: v.read_bytes() for k, v in paths.items()}
    result = inventory(*(data[k].decode("utf-8") for k in paths))
    result["source_sha256"] = {k: sha256(v).hexdigest() for k, v in data.items()}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "records"}, indent=2))


if __name__ == "__main__":
    main()
