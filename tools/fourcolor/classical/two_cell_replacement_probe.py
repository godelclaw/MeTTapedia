#!/usr/bin/env python3
"""Replay the two-cell seam obstruction and bounded replacement tests.

The Lean consumer checks the actual exterior, cut word and rejection by the
original patch. This independent program additionally closes the eight-cycle
replacement into a smaller spherical cubic map and checks a genuine colouring.
The bounded tree/wire census and abstract Kempe model are program evidence;
they do not rule out other replacements, recolouring, or stronger geometry.
"""
from __future__ import annotations

import argparse
from functools import cache
import hashlib
from itertools import product
import json
from pathlib import Path
import re

import networkx as nx

from dual_truncate_open_patch_probe import Map, decoded_rotation, edge
from dual_truncate_forest_probe import fixed_colourings, qualifies

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def ordered_patch(m):
    region, internal, ports = m.patch({0, 1})
    boundary = m.target.subgraph(region).copy()
    boundary.remove_edge((0, 1), (1, 0))
    assert all(degree == 2 for _, degree in boundary.degree())
    order = [min(boundary)]
    while len(order) < len(boundary):
        order.append(min(w for w in boundary[order[-1]] if w not in order))
    assert boundary.has_edge(order[-1], order[0])
    ordered = [next(e for e in ports if d in e) for d in order
               if any(d in e for e in ports)]
    assert len(ordered) == 8 and len(set(ordered)) == 8
    return region, internal, ordered, order


@cache
def trees(leaves):
    if leaves == 1:
        return (None,)
    return tuple((a, b) for k in range(1, leaves) for a in trees(k)
                 for b in trees(leaves - k))


@cache
def leaf_words(tree, colour):
    if tree is None:
        return ((colour,),)
    x, y = [v for v in (1, 2, 3) if v != colour]
    return tuple(a + b for d, e in [(x, y), (y, x)]
                 for a in leaf_words(tree[0], d) for b in leaf_words(tree[1], e))


@cache
def matchings(items):
    if not items:
        return ((),)
    return tuple(((items[0], items[j]),) + a + b for j in range(1, len(items), 2)
                 for a in matchings(items[1:j]) for b in matchings(items[j + 1:]))


def wire_relation(pairs):
    result = set()
    for cs in product((1, 2, 3), repeat=len(pairs)):
        word = [0] * (2 * len(pairs))
        for (i, j), c in zip(pairs, cs):
            word[i] = word[j] = c
        result.add(tuple(word))
    return result


def cycle_relation(n):
    return {tuple(es[i] ^ es[i - 1] for i in range(n))
            for es in product((1, 2, 3), repeat=n)
            if all(es[i] != es[i - 1] for i in range(n))}


def candidate_census(m):
    region, internal, ports, order = ordered_patch(m)
    observed = [m.polygon[e][1] for e in ports]
    assert all(observed.count(v) == 2 for v in set(observed))
    profiles = set()
    witnesses = 0
    for field in m.colourings(region, internal, ports):
        witnesses += 1
        profiles.add(tuple(field[e] for e in ports))
    labels = sorted(set(observed))
    paired = {tuple(cs[labels.index(v)] for v in observed)
              for cs in product((1, 2, 3), repeat=4)}

    def record(name, relation, kind, vertices):
        bad = sorted(relation - profiles)
        bad_paired = sorted((relation & paired) - profiles)
        return dict(name=name, kind=kind, interior_vertices=vertices,
                    support=len(relation), paired_support=len(relation & paired),
                    rejected=len(bad), rejected_paired=len(bad_paired),
                    first_rejected=bad[0] if bad else None,
                    first_rejected_paired=bad_paired[0] if bad_paired else None)

    candidates = [record("cycle8", cycle_relation(8), "cycle", 8)]
    candidates.extend(record("tree" + str(i),
                             {(c,) + w for c in (1, 2, 3) for w in leaf_words(t, c)},
                             "rooted plane cubic tree", 6) for i, t in enumerate(trees(7)))
    candidates.extend(record("wires" + str(i), wire_relation(p),
                             "noncrossing perfect wire pairing", 0)
                      for i, p in enumerate(matchings(tuple(range(8)))))
    assert len(candidates) == 147
    assert all(c["rejected"] > 0 for c in candidates)
    assert witnesses == 366 and len(profiles) == 327
    return profiles, paired, dict(
        actual_patch_vertices=len(region), actual_internal_edges=len(internal),
        actual_witnesses=witnesses, actual_profiles=len(profiles),
        paired_domain=len(paired), actual_paired_profiles=len(profiles & paired),
        candidates_checked=len(candidates), sound_over_full_boundary_domain=0,
        candidates=candidates,
        scope="Only the listed cycle, rooted plane trees and wire pairings were tested; "
              "paired-domain inclusion is insufficient for arbitrary smaller-map colourings.")


def canonical(word):
    labels = {}
    return tuple(labels.setdefault(c, len(labels) + 1) for c in word)


def abstract_kempe_model(profiles, paired):
    def parity(word):
        value = 0
        for c in word:
            value ^= c
        return value == 0

    states = {canonical(w) for w in product((1, 2, 3), repeat=8) if parity(w)}
    good = {canonical(w) for w in profiles}
    bad = states - good
    options = {}
    for w in sorted(bad):
        groups = []
        for a, b in [(1, 2), (1, 3), (2, 3)]:
            active = tuple(i for i, c in enumerate(w) if c in (a, b))
            assert len(active) % 2 == 0
            variants = []
            for pairs in matchings(active):
                targets = set()
                for mask in range(1 << len(pairs)):
                    x = list(w)
                    for j, (i, k) in enumerate(pairs):
                        if mask >> j & 1:
                            x[i] = a if x[i] == b else b
                            x[k] = a if x[k] == b else b
                    targets.add(canonical(x))
                variants.append(frozenset(targets))
            groups.append(variants)
        options[w] = groups
    current = bad.copy()
    rounds = []
    while True:
        killed = {w for w in current if any(not any(s <= current for s in opts)
                                           for opts in options[w])}
        if not killed:
            break
        current -= killed
        rounds.append(dict(removed=len(killed), remaining=len(current)))
    blocked = {canonical(w) for w in (cycle_relation(8) & paired) - profiles}
    assert states == good | bad and not good & current
    assert all(all(any(s <= current for s in opts) for opts in options[w]) for w in current)
    assert blocked <= current and len(current) == 213
    return dict(parity_orbits=len(states), good_orbits=len(good),
                initial_bad_orbits=len(bad), deletion_rounds=rounds,
                consistent_bad_orbits=len(current),
                paired_cycle_bad_orbits=sorted(blocked), bad_model=sorted(current),
                physical_exterior_realizing_entire_model_supplied=False,
                scope="Necessary parity, colour-permutation and noncrossing component-union "
                      "conditions admit a nonempty model avoiding the patch. No claim of "
                      "physical realizability, or impossibility under stronger geometry, is made.")


def closed_obstruction(m):
    text = (LEAN / "TwoCellCycleObstruction.lean").read_text()
    table = re.search(r"def exteriorWord.*?ByteArray.mk\s*#\[(.*?)\]", text, re.S)
    assert table
    values = list(map(int, re.findall(r"\d+", table.group(1))))
    assert len(values) == len(m.source) and values[:2] == [0, 0]
    c = dict(enumerate(values))
    selected = {0, 1}
    assert qualifies(m, selected)
    original_rows = {d: [m.alpha[d], m.phi[d], m.inverse[d]] for d in m.target}
    original_face_lengths = face_lengths(original_rows)
    assert original_face_lengths.count(5) == 12 and original_face_lengths.count(6) == 20
    assert all(c[v] != c[w] for v, w in m.source.edges()
               if v not in selected and w not in selected)
    base = m.reconstruct({d: c[d[0]] for d in m.alpha})
    region, _, ports, order = ordered_patch(m)
    assert all({base[edge(d, e)] for e in m.target[d]} == {1, 2, 3}
               for d in m.target if d not in region)
    word = tuple(base[e] for e in ports)
    assert word == (2, 2, 1, 1, 2, 2, 1, 1)
    assert not list(fixed_colourings(m, selected, base))
    cycle = None
    for start in (1, 2, 3):
        es, current = [], start
        for y in word:
            current ^= y
            if current == 0:
                break
            es.append(current)
        else:
            if current == start:
                cycle = es
                break
    assert cycle and all(cycle[i - 1] ^ cycle[i] == word[i] for i in range(8))
    rows = {("outside", d): [("outside", e) if e not in region
                             else ("cycle", ports.index(edge(d, e)))
                             for e in (m.alpha[d], m.phi[d], m.inverse[d])]
            for d in m.target if d not in region}
    for i, e in enumerate(ports):
        ext = next(d for d in e if d not in region)
        rows["cycle", i] = [("outside", ext), ("cycle", (i - 1) % 8), ("cycle", (i + 1) % 8)]
    small = nx.Graph((v, w) for v, ws in rows.items() for w in ws)
    assert all(deg == 3 for _, deg in small.degree())
    assert nx.is_connected(small) and not list(nx.bridges(small))
    small_face_lengths = face_lengths(rows)
    field = {}
    for v, w in small.edges():
        if v[0] == "outside" and w[0] == "outside":
            field[edge(v, w)] = base[edge(v[1], w[1])]
        elif v[0] == "cycle" and w[0] == "cycle":
            i, j = v[1], w[1]
            field[edge(v, w)] = cycle[i] if j == (i + 1) % 8 else cycle[j]
        else:
            i = v[1] if v[0] == "cycle" else w[1]
            field[edge(v, w)] = word[i]
    assert all({field[edge(v, w)] for w in small[v]} == {1, 2, 3} for v in small)
    return dict(source_cyclic_neighbours=m.raw, exterior_source_values=values,
                boundary_source_vertices=[m.polygon[e][1] for e in ports],
                boundary_word=word, cycle_edge_colours=cycle,
                original_vertices=len(m.target), smaller_vertices=len(small),
                patch_vertices=len(region), replacement_vertices=8,
                fixed_exterior_vertices=len(small) - 8,
                smaller_spherical_cubic_connected_bridgeless=True,
                smaller_tait_witness=True, original_fixed_exterior_extensions=0,
                original_face_lengths=original_face_lengths,
                smaller_face_lengths=small_face_lengths,
                closed_smaller_map_kernel_certified=False,
                original_has_only_pentagonal_and_hexagonal_faces=True,
                minimal_counterexample_hypotheses_supplied=False,
                scope="This direct cycle replacement cannot reconstruct this supplied "
                      "exterior. Recolouring and other decompositions remain available.")


def face_lengths(rows):
    alpha = {(v, w): (w, v) for v in rows for w in rows[v]}
    rho = {(v, w): (v, rows[v][(j + 1) % 3]) for v in rows for j, w in enumerate(rows[v])}
    phi = {d: rho[alpha[d]] for d in alpha}
    seen, lengths = set(), []
    for d in phi:
        if d in seen:
            continue
        x, length = d, 0
        while x not in seen:
            seen.add(x)
            length += 1
            x = phi[x]
        assert x == d
        lengths.append(length)
    assert len(rows) - len(alpha) // 2 + len(lengths) == 2
    return lengths


def run():
    m = Map("dodecahedral-expansion", decoded_rotation("TwoCellCycleObstruction.lean"))
    profiles, paired, census = candidate_census(m)
    paths = [Path(__file__), HERE / "dual_truncate_open_patch_probe.py",
             HERE / "dual_truncate_geometry_probe.py", HERE / "dual_truncate_forest_probe.py"]
    paths.extend(LEAN / name for name in ["TwoCellBoundaryChoice.lean",
                 "TwoCellCycleObstruction.lean", "TwoCellCycleObstructionAudit.lean",
                 "DualTruncateForestCollapse.lean", "DualTruncateCornerSemantics.lean",
                 "CubicRotationByteCertificate.lean", "CycleCapTangle.lean"])
    return dict(status="independent exact two-cell replacement replay", kernel_certified_replay=False,
                closed_obstruction=closed_obstruction(m), candidate_census=census,
                abstract_kempe_necessary_conditions=abstract_kempe_model(profiles, paired),
                new_uniform_strict_reduction=False, new_catalogue_entries_removed=0,
                global_coverage_proved=False,
                input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "two-cell-replacement-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report = run()
    data = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == data, "Two-cell replay receipt differs."
    else:
        args.output.write_text(data)
    print(json.dumps(dict(candidate_count=report["candidate_census"]["candidates_checked"],
                          closed_smaller_vertices=report["closed_obstruction"]["smaller_vertices"],
                          abstract_bad_orbits=report["abstract_kempe_necessary_conditions"]["consistent_bad_orbits"])))


if __name__ == "__main__":
    main()
