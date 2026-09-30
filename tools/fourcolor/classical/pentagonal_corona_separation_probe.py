#!/usr/bin/env python3
"""Replay simultaneous dart transports separating all corona vertex pairs.

This independent finite experiment uses the literal partial rotation diagram.
Its realization in an actual graph and the soundness of its terminal tests
are proved separately in Lean. No exterior or coverage claim is inferred.
"""

import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path


def diagram():
    """Outer vertices 0..10; central vertices 11..15; dart = 3*v + slot."""
    rotate = [
        3 * v + (s + (-1 if v < 11 and v % 2 == 0 else 1)) % 3
        for v in range(16) for s in range(3)
    ]
    flip = {}

    def join(a, b):
        assert a not in flip and b not in flip
        flip[a], flip[b] = b, a

    for i in range(11):
        join(3 * i + 2, 3 * ((i + 1) % 11) + 1)
    for i in range(5):
        join(3 * (11 + i), 3 * (11 + (i + 1) % 5) + 2)
        join(3 * (11 + i) + 1, 3 * (2 * ((-i) % 5) + 1))
    assert len(flip) == 42
    assert all(flip[flip[d]] == d for d in flip)
    assert all(rotate[rotate[rotate[d]]] == d for d in range(48))
    adjacency = {v: set() for v in range(16)}
    for d, e in flip.items():
        adjacency[d // 3].add(e // 3)
    assert all(v not in adjacency[v] for v in adjacency)
    return rotate, flip, adjacency


def shortest_paths(adjacency):
    paths = {}
    for start in adjacency:
        queue = deque([[start]])
        seen = {start}
        while queue:
            path = queue.popleft()
            paths[start, path[-1]] = path
            for v in sorted(adjacency[path[-1]]):
                if v not in seen:
                    seen.add(v)
                    queue.append(path + [v])
    return paths


def separate(a, b, threshold, rotate, flip, paths):
    queue = deque([(a, b, "")])
    seen = {(a, b)}
    while queue:
        x, y, word = queue.popleft()
        path = paths[x // 3, y // 3]
        if x != y and len(path) - 1 <= threshold:
            return {"word": word, "target_darts": [x, y], "vertex_path": path}
        steps = [(rotate[x], rotate[y], "r")]
        if x in flip and y in flip:
            steps.append((flip[x], flip[y], "a"))
        for xx, yy, letter in steps:
            if (xx, yy) not in seen:
                seen.add((xx, yy))
                queue.append((xx, yy, word + letter))
    return None


def verify_trace(source, trace, rotate, flip, adjacency):
    u, v, s = source
    x, y = 3 * u, 3 * v + s
    for letter in trace["word"]:
        if letter == "r":
            x, y = rotate[x], rotate[y]
        else:
            assert letter == "a" and x in flip and y in flip
            x, y = flip[x], flip[y]
    assert [x, y] == trace["target_darts"] and x != y
    path = trace["vertex_path"]
    assert path[0] == x // 3 and path[-1] == y // 3
    assert all(b in adjacency[a] for a, b in zip(path, path[1:]))
    assert len(path) <= 4


def probe():
    rotate, flip, adjacency = diagram()
    paths = shortest_paths(adjacency)
    summaries = []
    witnesses = []
    for threshold in (1, 2, 3):
        solved = []
        missing = []
        for u in range(16):
            for v in range(16):
                if u == v:
                    continue
                for s in range(3):
                    trace = separate(3 * u, 3 * v + s, threshold, rotate, flip, paths)
                    if trace is None:
                        missing.append([u, v, s])
                    else:
                        verify_trace([u, v, s], trace, rotate, flip, adjacency)
                        solved.append({"source": [u, v, s], **trace})
        summaries.append({"maximum_terminal_path_length": threshold,
                          "separated_pairs": len(solved), "unresolved_pairs": missing})
        if threshold == 3:
            witnesses = solved
    assert len(witnesses) == 720
    assert max(len(t["word"]) for t in witnesses) == 6
    flat = json.dumps(witnesses, sort_keys=True, separators=(",", ":")).encode()
    return {
        "scope": "Literal partial diagram; actual graph realization and semantic soundness are separate Lean theorems.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "vertices": 16,
        "darts": 48,
        "internal_darts": len(flip),
        "unpaired_darts": 48 - len(flip),
        "ordered_vertex_pair_phase_cases": len(witnesses),
        "maximum_transport_length": 6,
        "threshold_tests": summaries,
        "transport_length_histogram": dict(sorted(Counter(len(t["word"]) for t in witnesses).items())),
        "terminal_path_length_histogram": dict(sorted(Counter(len(t["vertex_path"]) - 1 for t in witnesses).items())),
        "longest_trace_example": next(t for t in witnesses if len(t["word"]) == 6),
        "all_deterministic_traces_sha256": hashlib.sha256(flat).hexdigest(),
        "trace_digest_encoding": "Source u, v, slot lexicographic order; JSON sorted keys and compact separators, UTF-8, no trailing newline.",
        "kernel_certification_of_this_program_output": False,
        "separate_kernel_check": "PentagonalCoronaSeparation.separates_all checks all 720 cases by decide at depth six.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name(
        "pentagonal-corona-separation-probe.json"))
    args = parser.parse_args()
    report = probe()
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Separated {report['ordered_vertex_pair_phase_cases']} cases in at most six operations.")
