#!/usr/bin/env python3
"""Replay physical exterior switches and joint two-cell reconstruction.

This program derives bichromatic components from the original graph and its
partial exterior field. It enumerates the eight port-touching one-component
swaps and reconstructs a whole-map witness after a successful joint choice.
The accompanying Lean proofs certify the selected saturated region, exterior
preservation, exact reconstruction and GSLT support. Component connectivity
and the census of all eight swaps are independent program checks.
"""
from __future__ import annotations

import argparse
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import re

import networkx as nx

from dual_truncate_open_patch_probe import Map, decoded_rotation, edge
from two_cell_replacement_probe import ordered_patch

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def source_values():
    text = (LEAN / "TwoCellCycleObstruction.lean").read_text()
    word = re.search(r"def exteriorWord.*?ByteArray\.mk #\[(.*?)\]", text, re.S)
    assert word
    return list(map(int, re.findall(r"\d+", word.group(1))))


def replay():
    m = Map("two-cell dodecahedral source", decoded_rotation("TwoCellCycleObstruction.lean"))
    values = source_values()
    assert len(values) == 20 and values[:2] == [0, 0]
    base = m.reconstruct({d: values[d[0]] for d in m.alpha})
    region, internal, ports, _ = ordered_patch(m)
    outside = set(m.target) - region
    assert len(region) == 10 and len(outside) == 50
    assert all({base[edge(d, e)] for e in m.target[d]} == {1, 2, 3} for d in outside)
    original_word = tuple(base[e] for e in ports)
    profiles = {tuple(field[e] for e in ports)
                for field in m.colourings(region, internal, ports)}
    assert original_word == (2, 2, 1, 1, 2, 2, 1, 1) and original_word not in profiles
    rows = [list(map(int, row.split(","))) for row in m.raw.split(";")]
    slot = lambda d: (d[0], rows[d[0]].index(d[1]))
    source_edges = sorted(tuple(sorted(e)) for e in m.source.edges())

    def actual_id(old):
        return ["polygon", list(slot(m.polygon[old]))] if old in m.polygon else \
            ["cross", source_edges.index(tuple(sorted((old[0][0], old[1][0]))))]

    cases, chosen = [], None
    for pair in combinations((1, 2, 3), 2):
        graph, originals = nx.Graph(), {}
        for d, e in m.target.edges():
            old = edge(d, e)
            if base[old] not in pair or (d in region and e in region):
                continue
            left = ("port", ports.index(old)) if d in region else ("vertex", d)
            right = ("port", ports.index(old)) if e in region else ("vertex", e)
            graph.add_edge(left, right)
            originals[edge(left, right)] = old
        components = sorted(nx.connected_components(graph), key=lambda vs: sorted(map(repr, vs)))
        for vertices in components:
            touched = sorted(v[1] for v in vertices if v[0] == "port")
            if not touched:
                continue
            assert len(touched) == 2
            component = graph.subgraph(vertices)
            assert nx.is_tree(component) and all(k <= 2 for _, k in component.degree())
            selected = {originals[edge(a, b)] for a, b in component.edges()}
            switched = {e: pair[1] if c == pair[0] else pair[0] if c == pair[1] else c
                        for e, c in base.items() if e in selected}
            field = base | switched
            assert all({field[edge(d, e)] for e in m.target[d]} == {1, 2, 3} for d in outside)
            word = tuple(field[e] for e in ports)
            paired = all(word[i] == word[i + 1] for i in (0, 2, 4, 6))
            cases.append(dict(pair=list(pair), ports=touched, selected_edges=len(selected),
                              boundary=list(word), accepted=word in profiles, paired=paired))
            if pair == (1, 3) and touched == [6, 7]:
                path = nx.shortest_path(component, ("port", 6), ("port", 7))
                q = m.corners(field)
                exterior_choices = {}
                for d in m.alpha:
                    if d[0] not in {0, 1}:
                        assert d in outside or m.inverse[d] in outside
                        previous = exterior_choices.setdefault(d[0], q[d])
                        assert previous == q[d]
                # The selected source values are chosen jointly, including their edge.
                choices = [(x, y) for x, y in product((1, 2, 3), repeat=2)
                           if x != y and x not in (exterior_choices[10], exterior_choices[19])
                           and y not in (exterior_choices[2], exterior_choices[8])]
                assert choices == [(1, 3)]
                new_source = exterior_choices | {0: choices[0][0], 1: choices[0][1]}
                full = m.source_field(new_source)
                assert m.valid(m.corners(full))
                assert all({full[edge(d, e)] for e in m.target[d]} == {1, 2, 3} for d in m.target)
                visible = {edge(d, e) for d in outside for e in m.target[d]}
                assert all(full[e] == field[e] for e in visible)
                changed_source = [v for v in sorted(exterior_choices) if exterior_choices[v] != values[v]]
                assert changed_source == [3, 4, 17, 19]
                chosen = dict(pair=list(pair), ports=touched, selected_edges=len(selected),
                              outside_vertices=len(vertices) - 2, boundary=list(word),
                              source_vertices_switched=changed_source,
                              joint_choices=[list(choice) for choice in choices],
                              actual_path_edges=[actual_id(originals[edge(a, b)])
                                                 for a, b in zip(path, path[1:])],
                              actual_path_vertices=[list(slot(v[1])) for v in path[1:-1]],
                              whole_map_reconstructed=True, all_visible_edges_preserved=True)
    assert len(cases) == 8 and sum(c["accepted"] for c in cases) == 4
    assert chosen and chosen["selected_edges"] == 17 and chosen["outside_vertices"] == 16
    sources = ["TwoCellCycleObstruction.lean", "TwoCellBoundaryChoiceRepair.lean",
               "RotationPatchKempe.lean", "SourcePatchKempe.lean", "TwoCellPhysicalKempeRepair.lean"]
    return dict(schema=1, evidence="independent program replay", source_vertices=20,
                target_vertices=60, patch_vertices=10, exterior_vertices=50,
                original_boundary=list(original_word), original_extension=False,
                swaps_checked=8, accepted_swaps=4, cases=cases, chosen=chosen,
                new_strict_reduction=False, new_coverage=False, catalogue_entries_removed=0,
                source_sha256={name: hashlib.sha256((LEAN / name).read_bytes()).hexdigest()
                               for name in sources})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = replay()
    record = HERE / "two-cell-physical-repair-probe.json"
    if args.check:
        assert json.loads(record.read_text()) == result, "Replay differs from checked-in record"
    else:
        record.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Checked {result['swaps_checked']} actual swaps; {result['accepted_swaps']} repair the patch; "
          f"{result['chosen']['selected_edges']} selected edges reconstruct the whole map.")


if __name__ == "__main__":
    main()
