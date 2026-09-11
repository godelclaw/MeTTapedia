#!/usr/bin/env python3
"""Check permutation-free rotation data before its coverage proof.

Pre-registered: each valid incidence code determines exactly one edge flip;
each vertex has exactly two cyclic rotations. At bound two the raw compact
carrier has 3252 codes, 145 valid rotations (including the empty code),
72 spherical connected bridgeless codes, and no uncolourable accepted code.
This is a tiny multigraph-code audit, not a useful global reduction base.
"""

import itertools
import json

from v24_bounded_cubic_trace_gate import assignments
from v24_bounded_rotation_code_gate import face_count, rotation
from v24_bounded_trace_topology_gate import topology


def gate():
    derangements = [p for p in itertools.permutations(range(3))
                    if all(p[i] != i for i in range(3))]
    assert derangements == [(1, 2, 0), (2, 0, 1)]
    counts = dict(raw=0, valid=0, admissible=0, bad=0)
    for n in range(3):
        for m in range(4):
            for flat in itertools.product(range(m), repeat=3 * n):
                stars = [flat[3 * v:3 * v + 3] for v in range(n)]
                for signs in itertools.product((False, True), repeat=n):
                    counts["raw"] += 1
                    try:
                        topo = topology(stars, m)
                    except ValueError:
                        continue
                    alpha, rho = rotation(stars, m, signs)
                    for d in range(3 * n):
                        mates = [e for e in range(3 * n)
                                 if e // 3 != d // 3 and flat[e] == flat[d]]
                        assert mates == [alpha[d]]
                    counts["valid"] += 1
                    if (topo["connected"] and not topo["bridges"] and
                            n - m + face_count(alpha, rho) == 2):
                        counts["admissible"] += 1
                        counts["bad"] += not assignments(stars, m)
    assert counts == dict(raw=3252, valid=145, admissible=72, bad=0)
    return dict(status="pass", bound=2, counts=counts,
                local_rotations=[list(p) for p in derangements],
                scope="All tiny multigraph codes; no global threshold or simple-map base claim.")


if __name__ == "__main__":
    print(json.dumps(gate(), sort_keys=True, indent=2))
