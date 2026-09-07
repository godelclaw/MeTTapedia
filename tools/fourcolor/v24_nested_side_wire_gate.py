#!/usr/bin/env python3
"""Preregistered ambient nested-side composition gate.

Use every nested pair of the complete cyclic prism cuts in the marked-cotree
control. Restriction and gluing must be inverse on literal retained darts;
proper side colourings must correspond exactly to proper inner/slab
colourings agreeing on the internal seam. Outer words must additionally
copy the input word on persistent crossing darts. Deleting that equality
must fail the deliberate wire-word mutation controls.
Equal pairs test the empty material layer: its transfer is the identity.
The identity is restricted to nonzero Tait words: matching zero colours on
a wire must be rejected even though they satisfy its equality equation.

This tests generic composition on given colour assignments. It produces
no support table, reducibility certificate or configuration catalogue.
Outcomes: geometry_failure, composition_failure, wire_failure, passed.
"""

import argparse
import itertools
import json
from pathlib import Path
import random

from v24_annular_census import atomic_write_json
from v24_marked_cotree_gate import frozen_edge_control


def audit():
    control = frozen_edge_control()
    edges = control["graph"]["primal_edges"]
    darts = [(u, v) for a, b in edges for u, v in ((a, b), (b, a))]
    rng = random.Random(1729)

    def restrict(c, side):
        return {d: c[d] for d in darts if d[0] in side}

    def good(c, side):
        assert set(c) == {d for d in darts if d[0] in side}
        return (all(c[d] != 0 for d in c)
                and all(len({c[d] for d in c if d[0] == v}) == 3 for v in side)
                and all(c[u, v] == c[v, u] for u, v in c if v in side))

    def boundary(side):
        return [d for d in darts if d[0] in side and d[1] not in side]

    def seam_agrees(inner, slab, ci, cs):
        return all(ci[u, v] == cs[v, u] for u, v in boundary(inner) if v in slab)

    def relation_parts(inner, outer, cs, x, y):
        slab = outer - inner
        material = (good(cs, slab)
                    and all(cs[v, u] == x[u, v]
                            for u, v in boundary(inner) if v in slab)
                    and all(cs[d] == y[d] for d in boundary(outer) if d[0] in slab))
        wires = all(x[d] == y[d] and x[d] != 0
                    for d in boundary(outer) if d[0] in inner)
        return material, wires

    rows = []
    for a, b in itertools.combinations_with_replacement(control["prefix_rungs"], 2):
        inner = set(range(a)) | set(range(8, 8 + a))
        outer = set(range(b)) | set(range(8, 8 + b))
        slab = outer - inner
        assert inner <= outer and bool(slab) == (a < b), "geometry_failure"
        through = [d for d in boundary(outer) if d[0] in inner]
        assert len(through) == (2 if a < b else 4)
        fixed = {(0, 7), (7, 0)}
        assert all(d[0] not in slab for d in fixed), "geometry_failure"
        tested, positive, mutations, zero_mutations, seam_mutations = 0, 0, 0, 0, 0
        cases = []
        # A known Tait colouring of the even prism: alternating ring
        # colours and a third spoke colour. Apply all global permutations.
        for colors in itertools.permutations((1, 2, 3)):
            c = {}
            for u, v in darts:
                if abs(u - v) == 8:
                    ci = 2
                else:
                    lo, hi = sorted((u % 8, v % 8))
                    ci = 1 if (lo, hi) == (0, 7) else lo % 2
                c[u, v] = colors[ci]
            assert good(c, set(range(16))), "composition_failure"
            cases.append(restrict(c, outer))
        for _ in range(4096):
            cases.append({d: rng.randrange(4) for d in darts if d[0] in outer})
        for c in cases:
            ci, cs = restrict(c, inner), restrict(c, slab)
            glued = ci | cs
            assert glued == c and set(ci).isdisjoint(cs), "composition_failure"
            assert all(c[d] == 1 for d in fixed if d in c) == all(
                ci[d] == 1 for d in fixed if d in ci), "wire_failure"
            assert good(c, outer) == (good(ci, inner) and good(cs, slab)
                                      and seam_agrees(inner, slab, ci, cs))
            x = {d: ci[d] for d in boundary(inner)}
            y = {d: c[d] for d in boundary(outer)}
            material, wires = relation_parts(inner, outer, cs, x, y)
            assert good(c, outer) == (good(ci, inner) and material and wires)
            if a == b:
                assert not cs and material and x == y, "wire_failure"
                assert wires == all(x[d] != 0 for d in x), "wire_failure"
            tested += 1
            if good(c, outer):
                positive += 1
                if slab:
                    wrong_slab = {d: cs[d] % 3 + 1 for d in cs}
                    assert good(ci, inner) and good(wrong_slab, slab)
                    assert not seam_agrees(inner, slab, ci, wrong_slab)
                    wrong_glued = ci | wrong_slab
                    assert not good(wrong_glued, outer), "composition_failure"
                    wrong_y = {d: wrong_glued[d] for d in boundary(outer)}
                    material, wires = relation_parts(inner, outer, wrong_slab, x, wrong_y)
                    assert not material and wires, "composition_failure"
                    seam_mutations += 1
                for d in through:
                    wrong = dict(y)
                    wrong[d] = y[d] % 3 + 1
                    material, wires = relation_parts(inner, outer, cs, x, wrong)
                    assert material and not wires, "wire_failure"
                    assert wrong[d] != glued[d], "wire_failure"
                    mutations += 1
                    zero_x, zero_y = dict(x), dict(y)
                    zero_x[d] = zero_y[d] = 0
                    material, wires = relation_parts(inner, outer, cs, zero_x, zero_y)
                    assert material and not wires, "wire_failure"
                    zero_mutations += 1
        rows.append(dict(inner_rungs=a, outer_rungs=b, slab_vertices=len(slab),
                         through_darts=[list(d) for d in through],
                         assignments=tested, proper_assignments=positive,
                         fixed_dart_assignments=tested,
                         rejected_wire_mutations=mutations,
                         rejected_zero_wire_mutations=zero_mutations,
                         rejected_seam_mutations=seam_mutations))
    return dict(schema="fourcolor-v24-nested-side-wire-v1", control=control,
                cases=rows, outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    result = audit()
    assert result == json.loads(json.dumps(result))
    if args.output:
        atomic_write_json(args.output, result)
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
