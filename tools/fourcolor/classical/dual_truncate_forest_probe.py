#!/usr/bin/env python3
"""Replay exact source-choice collapse on separated forest patches.

Only exterior source values are supplied. Selected source values are zero
until genuine patch witnesses or source assignments reconstruct them. Small
subset tests and longer paths exercise the same family contract; these
independent program checks do not supply the general Lean proof.
"""
from __future__ import annotations

import argparse
import hashlib
from itertools import permutations, product
import json
from pathlib import Path

import networkx as nx

from dual_truncate_open_patch_probe import Map, cube_rotation, decoded_rotation, edge

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def qualifies(m, selected):
    forest = not selected or nx.is_forest(m.source.subgraph(selected))
    separated = all(sum(w in selected for w in m.source[v]) <= 1
                    for v in m.source if v not in selected)
    return forest and separated


def fixed_colourings(m, selected, base):
    region, _, ports = m.patch(selected)
    values = {e: base[e] for e in ports}
    stars = {d: tuple(edge(d, e) for e in sorted(m.target[d])) for d in region}
    choices = list(permutations((1, 2, 3)))

    def visit(left):
        if not left:
            yield dict(values)
            return
        d = max(left, key=lambda d: (sum(e in values for e in stars[d]), d))
        newly = [e for e in stars[d] if e not in values]
        for cs in choices:
            if any(e in values and values[e] != c for e, c in zip(stars[d], cs)):
                continue
            values.update(zip(stars[d], cs))
            yield from visit(left - {d})
            for e in newly:
                del values[e]

    yield from visit(region)


def replay(m, selected, exterior_values):
    assert qualifies(m, selected)
    c = {v: 0 if v in selected else exterior_values[v] for v in m.source}
    assert all(c[v] == 0 for v in selected)
    base = m.reconstruct({d: c[d[0]] for d in m.alpha})
    region, internal, ports = m.patch(selected)
    for d in set(m.target) - region:
        assert {base[edge(d, e)] for e in m.target[d]} == {1, 2, 3}
    observed = {d for d in m.alpha if d not in region or m.inverse[d] not in region}
    assert all(d[0] not in selected for d in observed)
    assert all(m.corners(base)[d] == c[d[0]] for d in observed)
    actual = set()
    for patch in fixed_colourings(m, selected, base):
        full = dict(base)
        full.update(patch)
        q = m.corners(full)
        assert m.valid(q) and m.coherent(q)
        assert all(full[e] == base[e] for e in full if e not in internal)
        recovered = {v: q[next(d for d in m.alpha if d[0] == v)] for v in m.source}
        assert all(recovered[v] == c[v] for v in m.source if v not in selected)
        assert m.source_field(recovered) == full
        signature = tuple(recovered[v] for v in sorted(selected))
        assert signature not in actual
        actual.add(signature)
    source = set()
    for word in product((1, 2, 3), repeat=len(selected)):
        assignment = dict(c)
        assignment.update(zip(sorted(selected), word))
        if all(assignment[d[0]] != assignment[d[1]] for d in m.alpha):
            source.add(word)
    assert actual == source
    return dict(name=m.name, selected=sorted(selected), actual_witnesses=len(actual),
                source_witnesses=len(source), all_witnesses_coherent=True,
                exterior_source_values=[c[v] for v in sorted(m.source)],
                target_vertices=len(m.target), target_patch_vertices=len(region),
                fixed_exterior_vertices=len(m.target) - len(region),
                internal_edge_variables=len(internal), retained_source_variables=len(selected),
                ports=len(ports))


def run():
    cube = Map("cube", cube_rotation())
    prism = Map("triangular-prism", decoded_rotation("DualTruncateSourceDomainExample.lean"))
    results = []
    for m, c in [(cube, dict(enumerate([2, 1, 2, 1, 1, 2, 1, 2]))),
                 (prism, dict(enumerate([1, 2, 3, 2, 3, 1])))]:
        for mask in range(1 << len(m.source)):
            selected = {v for v in m.source if mask >> v & 1}
            if qualifies(m, selected):
                results.append(replay(m, selected, c))
    generated_maps = []
    for n in [6, 8, 10, 12]:
        g = nx.circular_ladder_graph(n)
        planar, embedding = nx.check_planarity(g)
        assert planar
        raw = ";".join(",".join(map(str, embedding.neighbors_cw_order(v))) for v in range(2 * n))
        m = Map("circular-prism-" + str(n), raw)
        c = {v: 1 + colour for v, colour in nx.bipartite.color(g).items()}
        generated_maps.append(dict(name=m.name, cyclic_neighbours=raw))
        for k in [1, 2, 3, n - 2]:
            results.append(replay(m, set(range(k)), c))
    g = nx.dodecahedral_graph()
    planar, embedding = nx.check_planarity(g)
    assert planar
    raw = ";".join(",".join(map(str, embedding.neighbors_cw_order(v))) for v in range(20))
    m = Map("dodecahedral-source", raw)
    c = dict(enumerate([1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 3]))
    assert set(c.values()) == {1, 2, 3}
    face_lengths = []
    seen = set()
    for d in m.phi:
        if d in seen:
            continue
        start, x, length = d, d, 0
        while x not in seen:
            seen.add(x)
            length += 1
            x = m.phi[x]
        assert x == start
        face_lengths.append(length)
    assert face_lengths == [5] * 12
    generated_maps.append(dict(name=m.name, cyclic_neighbours=raw, source_face_lengths=face_lengths,
                               target_vertices=60, kernel_certified_fixture=False))
    for selected in [{0}, {0, 1}, {0, 1, 2}, {0, 1, 2, 6, 5}, {0, 1, 2, 6, 5, 15}]:
        results.append(replay(m, selected, c))
    assert not qualifies(cube, {0, 1, 2})
    kernel = next(r for r in results if r["name"] == "cube" and r["selected"] == [0, 1])
    assert kernel["actual_witnesses"] == 3 and kernel["internal_edge_variables"] == 11
    paths = [Path(__file__), HERE / "dual_truncate_open_patch_probe.py",
             HERE / "dual_truncate_geometry_probe.py", HERE / "alternating_cycle_probe.py",
             LEAN.parent / "FiniteForestBranching.lean"]
    paths.extend(LEAN / name for name in ["DualTruncateForestCollapse.lean",
                 "DualTruncateForestExample.lean", "DualTruncateForestAudit.lean",
                 "DualTruncateCornerSemantics.lean", "DualTruncateCornerCoherence.lean",
                 "DualTruncateOpenPatch.lean", "DualTruncateOpenPatchExample.lean",
                 "DualTruncateCoupledExample.lean", "DualTruncateSourceDomainExample.lean"])
    return dict(status="independent exact separated-forest replay", kernel_certified_replay=False,
                checked_patches=len(results), checked_witnesses=sum(r["actual_witnesses"] for r in results),
                results=results, generated_maps=generated_maps,
                kernel_two_cell_consumer=kernel, exterior_input_has_zero_selected_values=True,
                cube_three_cell_excluded_by_separation=True,
                all_actual_witnesses_retained=True, counts_preserved=True,
                executable_recolouring_history_preserved=False,
                new_smaller_embedded_graph_operation=False, new_catalogue_entries_removed=0,
                global_coverage_proved=False, classical_endpoint_used=False,
                input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "dual-truncate-forest-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report = run()
    data = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == data, "Forest replay receipt differs."
    else:
        args.output.write_text(data)
    print(json.dumps({k: report[k] for k in ["checked_patches", "checked_witnesses"]}, sort_keys=True))


if __name__ == "__main__":
    main()
