#!/usr/bin/env python3
"""Replay exact corner elimination and fixed-exterior patch reconstruction.

Exhaust source vertex subsets of three small literal maps. Actual target
colourings are projected to polygon-corner states and reconstructed. Paired
boundary profiles and source vertex-colouring profiles are compared separately
on named patches. These program checks do not supply the general Lean proofs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import permutations, product
import json
from pathlib import Path
import re

import networkx as nx

from dual_truncate_geometry_probe import cube_rotation, rotation_data

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def decoded_rotation(filename: str) -> str:
    text = (LEAN / filename).read_text()
    table = re.search(r"neighbours\s*:=.*?ByteArray\.mk\s*#\[(.*?)\]", text, re.S)
    assert table
    flat = bytes(map(int, re.findall(r"\d+", table.group(1))))
    entries = [int.from_bytes(flat[i:i + 2], "little") for i in range(0, len(flat), 2)]
    return ";".join(",".join(map(str, entries[i:i + 3])) for i in range(0, len(entries), 3))


def edge(a, b):
    return tuple(sorted((a, b)))


class Map:
    def __init__(self, name: str, raw: str):
        self.name, self.raw = name, raw
        self.source, self.alpha, self.rho = rotation_data(raw)
        self.phi = {d: self.rho[self.alpha[d]] for d in self.alpha}
        self.inverse = {v: d for d, v in self.phi.items()}
        self.target = nx.Graph((d, e) for d in self.alpha
                               for e in (self.alpha[d], self.phi[d], self.inverse[d]))
        assert all(degree == 3 for _, degree in self.target.degree())
        self.cross = {edge(d, self.alpha[d]) for d in self.alpha}
        self.polygon = {edge(d, self.phi[d]): d for d in self.alpha}
        assert len(self.polygon) == len(self.alpha)
        assert self.cross.isdisjoint(self.polygon)

    def corners(self, field):
        return {d: field[edge(self.inverse[d], d)] for d in self.alpha}

    def reconstruct(self, q):
        f = {}
        for d in self.alpha:
            e = edge(d, self.alpha[d])
            value = q[d] ^ q[self.phi[d]]
            assert e not in f or f[e] == value
            f[e] = value
            f[edge(d, self.phi[d])] = q[self.phi[d]]
        return f

    def source_field(self, c):
        assert all(c[d[0]] != c[d[1]] for d in self.alpha)
        return self.reconstruct({d: c[d[0]] for d in self.alpha})

    def valid(self, q):
        return all(q[d] in (1, 2, 3) and q[d] != q[self.phi[d]] and
                   q[d] ^ q[self.phi[d]] == q[self.alpha[d]] ^ q[self.phi[self.alpha[d]]]
                   for d in self.alpha)

    def coherent(self, q):
        return all(q[d] == q[self.rho[d]] for d in self.alpha)

    def patch(self, selected):
        region = {d for d in self.alpha if d[0] in selected or d[1] in selected}
        assert all((d in region) == (self.alpha[d] in region) for d in self.alpha)
        internal = sorted(edge(d, e) for d, e in self.target.subgraph(region).edges())
        ports = sorted(edge(d, e) for d, e in self.target.edges()
                       if (d in region) != (e in region))
        assert all(e in self.polygon for e in ports)
        return region, internal, ports

    def colourings(self, region, internal, ports):
        edges = sorted(set(internal + ports))
        ids = {e: i for i, e in enumerate(edges)}
        stars = {d: tuple(ids[edge(d, e)] for e in sorted(self.target[d])) for d in region}
        values = [0] * len(edges)
        choices = list(permutations((1, 2, 3)))

        def visit(left):
            if not left:
                yield dict(zip(edges, values))
                return
            d = max(left, key=lambda d: sum(values[e] != 0 for e in stars[d]))
            star = stars[d]
            newly_assigned = [e for e in star if not values[e]]
            for cs in choices:
                if any(values[e] and values[e] != c for e, c in zip(star, cs)):
                    continue
                for e, c in zip(star, cs):
                    values[e] = c
                yield from visit(left - {d})
                for e in newly_assigned:
                    values[e] = 0

        yield from visit(region)

    def replay(self, selected, baseline, compare_source=False):
        region, internal, ports = self.patch(selected)
        variables = sorted(self.phi[self.polygon[e]] for e in internal + ports if e in self.polygon)
        assert len(set(variables)) == len(variables)
        signatures, paired = set(), Counter()
        total = completions = varying_completions = 0
        for field in self.colourings(region, internal, ports):
            total += 1
            q = {d: field[edge(self.inverse[d], d)] for d in variables}
            signature = tuple(q[d] for d in variables)
            assert signature not in signatures
            signatures.add(signature)
            for d in region:
                assert q[d] in (1, 2, 3) and q[self.phi[d]] in (1, 2, 3)
                assert q[d] != q[self.phi[d]]
                assert q[d] ^ q[self.phi[d]] == q[self.alpha[d]] ^ q[self.phi[self.alpha[d]]]
                assert field[edge(d, self.alpha[d])] == q[d] ^ q[self.phi[d]]
                assert field[edge(d, self.phi[d])] == q[self.phi[d]]
            if all(field[e] == baseline[e] for e in ports):
                full = dict(baseline)
                full.update(field)
                corners = self.corners(full)
                assert self.valid(corners) and self.reconstruct(corners) == full
                assert all(full[e] == baseline[e] for e in full if e not in internal)
                completions += 1
                varying_completions += not self.coherent(corners)
            if compare_source:
                by = {}
                for e in ports:
                    vertex = self.polygon[e][1]
                    assert vertex not in selected
                    if vertex in by and by[vertex] != field[e]:
                        break
                    by[vertex] = field[e]
                else:
                    paired[tuple(sorted(by.items()))] += 1
        report = dict(selected_source_vertices=sorted(selected), target_patch_vertices=len(region),
                      ports=len(ports), internal_edge_variables=len(internal),
                      retained_internal_polygon_variables=sum(e in self.polygon for e in internal),
                      cross_variables_eliminated=sum(e in self.cross for e in internal),
                      actual_patch_witnesses=total, exact_corner_states=len(signatures),
                      fixed_exterior_witnesses=completions,
                      fixed_exterior_witnesses_with_varying_corners=varying_completions)
        if compare_source:
            observed = sorted({self.polygon[e][1] for e in ports})
            neighbours = {d[1] for d in self.alpha if d[0] in selected} - set(selected)
            assert neighbours <= set(observed), "A hidden exterior source colour needs a separate contract."
            profiles = {}
            for outside in product((1, 2, 3), repeat=len(observed)):
                c = dict(zip(observed, outside))
                count = 0
                for inside in product((1, 2, 3), repeat=len(selected)):
                    c.update(zip(sorted(selected), inside))
                    count += all(c[d[0]] != c[d[1]] for d in self.alpha if d[0] in selected)
                profiles[tuple(zip(observed, outside))] = count
            differences = [dict(boundary=list(w), patch_witnesses=paired[w], source_witnesses=n)
                           for w, n in profiles.items() if paired[w] != n]
            report.update(paired_profiles=len(paired), paired_patch_witnesses=sum(paired.values()),
                          source_compatible_witnesses=sum(profiles.values()),
                          fibre_count_mismatches=len(differences),
                          support_mismatches=sum(bool(paired[w]) != bool(n) for w, n in profiles.items()),
                          mismatch_examples=differences[:2])
        return report


def run():
    cube = Map("cube", cube_rotation())
    prism = Map("triangular-prism", decoded_rotation("DualTruncateSourceDomainExample.lean"))
    planar, embedding = nx.check_planarity(nx.complete_graph(4))
    assert planar
    raw = ";".join(",".join(map(str, embedding.neighbors_cw_order(v))) for v in range(4))
    tetrahedron = Map("four-clique", raw)
    cube_base = cube.source_field(dict(enumerate([2, 1, 2, 1, 1, 2, 1, 2])))
    prism_base = prism.source_field(dict(enumerate([1, 2, 3, 2, 3, 1])))
    r, internal, ports = tetrahedron.patch(set(range(4)))
    tetrahedron_base = next(tetrahedron.colourings(r, internal, ports))
    maps = [(cube, cube_base), (prism, prism_base), (tetrahedron, tetrahedron_base)]
    totals = Counter()
    all_subsets = []
    for m, baseline in maps:
        subtotal = Counter()
        for mask in range(1 << len(m.source)):
            selected = {v for v in m.source if mask & (1 << v)}
            report = m.replay(selected, baseline)
            subtotal["patches"] += 1
            subtotal["actual_witnesses"] += report["actual_patch_witnesses"]
            subtotal["exact_corner_states"] += report["exact_corner_states"]
            subtotal["fixed_exterior_witnesses"] += report["fixed_exterior_witnesses"]
        assert subtotal["actual_witnesses"] == subtotal["exact_corner_states"]
        totals.update(subtotal)
        all_subsets.append(dict(name=m.name, source_vertices=len(m.source),
                                target_vertices=len(m.target), **subtotal))
    named = []
    for m, baseline in maps:
        selected_sets = [{0}, {0, 1}, {0, 1, 2}] if m != tetrahedron else [set(range(4))]
        for selected in selected_sets:
            named.append(dict(name=m.name, **m.replay(selected, baseline, compare_source=True)))
    cube_three = next(r for r in named if r["name"] == "cube" and r["selected_source_vertices"] == [0, 1, 2])
    assert cube_three["fixed_exterior_witnesses"] == 7
    assert cube_three["fixed_exterior_witnesses_with_varying_corners"] == 2
    assert cube_three["paired_patch_witnesses"] == 192 and cube_three["source_compatible_witnesses"] == 144
    assert cube_three["support_mismatches"] == 0
    clique = named[-1]
    assert clique["actual_patch_witnesses"] == 6 and clique["source_compatible_witnesses"] == 0
    fixture = (LEAN / "DualTruncateOpenPatchExample.lean").read_text()
    table = re.search(r"cornerWord.*?ByteArray\.mk\s*#\[(.*?)\]", fixture, re.S)
    assert table
    word = list(map(int, re.findall(r"\d+", table.group(1))))
    order = [(v, int(w)) for v, row in enumerate(cube.raw.split(";")) for w in row.split(",")]
    q = dict(zip(order, word))
    assert len(q) == 24 and cube.valid(q) and not cube.coherent(q)
    recovered = cube.reconstruct(q)
    region, internal, ports = cube.patch({0, 1, 2})
    assert all(recovered[e] == cube_base[e] for e in recovered if e not in internal)
    assert q[order[0]] ^ q[cube.rho[order[0]]] == 2
    paths = [Path(__file__), HERE / "dual_truncate_geometry_probe.py",
             HERE / "alternating_cycle_probe.py", LEAN / "DualTruncateCoupledExample.lean",
             LEAN / "DualTruncateSourceDomainExample.lean"]
    paths.extend(LEAN / name for name in ["DualTruncateCornerSemantics.lean",
                                        "DualTruncateCornerCoherence.lean", "DualTruncateOpenPatch.lean",
                                        "DualTruncateOpenPatchExample.lean", "DualTruncateOpenPatchAudit.lean"])
    return dict(status="independent exact open-patch replay", all_source_subsets=all_subsets,
                totals=dict(totals), named_patches=named,
                kernel_fixture=dict(target_vertices=24, patch_vertices=14, exterior_vertices=10,
                                    internal_edge_variables=17, retained_internal_polygon_variables=10,
                                    eliminated_cross_variables=7, exterior_fixed=True,
                                    witness_has_varying_corners=True, matching_source_witness_exists=False),
                all_scope_colourings_retained_by_corner_summary=True,
                kernel_general_exact_equivalence=True,
                four_clique_obstruction_kernel_certified=False,
                new_smaller_embedded_graph_operation=False, new_catalogue_entries_removed=0,
                global_coverage_proved=False, classical_endpoint_used=False,
                input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "dual-truncate-open-patch-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report = run()
    data = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == data, "Open-patch replay receipt differs."
    else:
        args.output.write_text(data)
    print(json.dumps(report["totals"], sort_keys=True))


if __name__ == "__main__":
    main()
