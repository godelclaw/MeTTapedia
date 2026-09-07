#!/usr/bin/env python3
"""Check designated face orbits in literal full-interface surgery.

Preregistered claim: retaining the vertices of a named face, its old vertex
rotations, and its edge partners preserves its complete oriented face orbit.
Test every cyclic seam matching on nested cyclic strips of small prisms.
Require strict material, connected shores and complements, complete cuts,
and a face crossing the seam. Deliberately shifted matchings must be detected.
These colourable geometric controls are not target counterexamples, support
equalities, a colouring census, or a configuration catalogue.
"""

import argparse
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_geodesic_mincut_gate import connected, validate_sphere
from v24_goldberg import consistently_oriented_face_cycles
from v24_persistent_wire_order_gate import prism, single_cycle
from v24_tree_cotree_gate import return_permutation


def orbit(p, root):
    out, d = [], root
    while d not in out:
        out.append(d)
        d = p[d]
    assert d == root, "invalid_permutation"
    return out


def audit():
    pairs = preserved = rejected = crossing = 0
    specimen = None
    for k in range(6, 11):
        graph = prism(k)
        validate_sphere(graph)
        edges = graph["primal_edges"]
        faces = consistently_oriented_face_cycles(graph)
        darts = {(u, v) for a, b in edges for u, v in ((a, b), (b, a))}
        alpha = {(u, v): (v, u) for u, v in darts}
        phi = {}
        for face in faces:
            for i, v in enumerate(face):
                phi[(face[i - 1], v)] = (v, face[(i + 1) % len(face)])
        assert set(phi) == darts and set(phi.values()) == darts
        rho = {d: phi[alpha[d]] for d in darts}
        for a in range(2, k - 3):
            for b in range(a + 2, k - 1):
                A = set(range(a)) | set(range(k, k + a))
                B = set(range(b)) | set(range(k, k + b))
                U = set(range(2 * k))
                for side in (A, B, U - A, U - B):
                    assert connected(2 * k, edges, side)
                    assert sum(u in side and v in side for u, v in edges) >= len(side)
                inner = {i for i, (u, v) in enumerate(edges) if u in A or v in A}
                outer = {i for i, (u, v) in enumerate(edges) if u in B or v in B}
                assert inner < outer
                assert any(all(i in outer - inner for i, e in enumerate(edges) if v in e)
                           for v in B - A), "no_strict_star"
                ca = {i for i, (u, v) in enumerate(edges) if (u in A) != (v in A)}
                cb = {i for i, (u, v) in enumerate(edges) if (u in B) != (v in B)}
                assert len(ca) == len(cb) == 4
                pa = return_permutation(faces, A, ca, edges)
                pb = return_permutation(faces, B, cb, edges)
                assert single_cycle(pa) and single_cycle(pb)
                kept = A | (U - B)
                retained = {d for d in darts if d[0] in kept}
                root = (k - 1, 0)
                # Choose the rectangular face, not the long polygon face.
                if len(orbit(phi, root)) != 4:
                    root = alpha[root]
                old_face = orbit(phi, root)
                assert len(old_face) == 4 and set(old_face) <= retained
                named = set(old_face) | {alpha[d] for d in old_face}
                assert named <= retained
                left = {i: (v, u) if u in B else (u, v) for i in cb for u, v in [edges[i]]}
                right = {i: (u, v) if u in A else (v, u) for i in ca for u, v in [edges[i]]}
                pairs += 1
                for start in sorted(ca):
                    match = dict(zip(orbit(pb, min(cb)), orbit(pa, start)))
                    sewn_alpha = {d: alpha[d] for d in retained
                                  if (d[0] in A and d[1] in A) or
                                  (d[0] not in B and d[1] not in B)}
                    for i, j in match.items():
                        x, y = left[i], right[j]
                        sewn_alpha[x], sewn_alpha[y] = y, x
                    assert set(sewn_alpha) == retained
                    assert all(sewn_alpha[sewn_alpha[d]] == d and sewn_alpha[d] != d
                               for d in retained)
                    sewn_phi = {d: rho[sewn_alpha[d]] for d in retained}
                    same_edges = all(sewn_alpha[d] == alpha[d] for d in named)
                    same_face = orbit(sewn_phi, root) == old_face
                    if same_edges:
                        assert same_face, "face_preservation_failure"
                        assert len(orbit(sewn_phi, root)) == len(old_face)
                        preserved += 1
                        crossing += any(d in left.values() or d in right.values() for d in old_face)
                    elif not same_face:
                        rejected += 1
                        if specimen is None:
                            specimen = dict(prism=k, inner=sorted(A), outer=sorted(B),
                                            matching=sorted(match.items()), old_face=old_face,
                                            changed_face=orbit(sewn_phi, root))
    assert pairs and preserved == pairs and crossing == preserved and rejected, "insufficient_controls"
    return dict(status="passed", nested_pairs=pairs, preserved_crossing_faces=preserved,
                rejected_shifted_matchings=rejected, shifted_specimen=specimen,
                scope="full-interface geometry only; no zero-Count or support claim")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit()
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(result, indent=2))
