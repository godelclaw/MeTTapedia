#!/usr/bin/env python3
"""Replay diamond supply, density, and its relation to alternating lobes.

The census is independent program evidence, not a certificate of internal-six
connectivity or a universal coverage theorem. All first-return lobes are
examined, including those with an exceptional closing transition.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path

from alternating_lobe_probe import data, lobe_from, lobe_shores
from alternating_cycle_probe import alternating_orbits, graph_rotation, make_goldberg_graph

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def local_words():
    counts = {}
    for n in (5, 6):
        checked = forcing = 0
        for word in product((False, True), repeat=n):
            gaps = [i for i in range(n) if word[i] and word[(i + 2) % n]]
            assert sum(word) <= 2 or gaps
            checked += 1
            forcing += sum(word) > 2
        counts[n] = dict(checked=checked, with_three_or_more=forcing)
    return counts


def control(frequency):
    graph, alpha, rho = graph_rotation(make_goldberg_graph(frequency)["primal_edges"])
    rows = []
    for u in sorted(graph):
        dart = min(d for d in alpha if d[0] == u)
        rows.append(",".join(map(str, (dart[1], rho[dart][1], rho[rho[dart]][1]))))
    return dict(id=f"Goldberg-GP({frequency},0)", rotation=";".join(rows))


def inspect(raw):
    graph, alpha, rho, faces = data(raw["rotation"])
    phi = {d: rho[alpha[d]] for d in alpha}
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    length = lambda d: len(faces[face_of[d]])
    counts = [sum(length(alpha[d]) == 5 for d in face) for face in faces]
    assert sum(counts) == 5 * sum(len(f) == 5 for f in faces) == 60
    cores, occurrences = {}, []
    flanked = {d for d in alpha
               if length(rho[rho[d]]) == length(rho[rho[alpha[d]]]) == 5}
    for face in faces:
        n = len(face)
        word = [length(alpha[d]) == 5 for d in face]
        for i in range(n):
            assert (word[i] and word[(i + 2) % n]) == (face[(i + 1) % n] in flanked)
        assert sum(word) <= 2 or any(d in flanked for d in face)
    for dart in sorted(flanked):
        a, b = length(dart), length(alpha[dart])
        selected = {face_of[d] for d in
                    (dart, alpha[dart], rho[rho[dart]], rho[rho[alpha[dart]]])}
        assert len(selected) == 4
        if (a, b) == (5, 5):
            family, root = "six_port", phi[phi[phi[dart]]]
        elif (a, b) == (5, 6):
            family, root = "seven_port", dart
        elif (a, b) == (6, 5):
            family, root = "seven_port", alpha[dart]
        else:
            assert (a, b) == (6, 6)
            family, root = "eight_port", dart
        central = [root]
        for _ in range(length(root) - 1):
            central.append(phi[central[-1]])
        indices = (1, 2, 3) if family == "six_port" else (0, 1, len(central) - 1)
        expected = [5, 5, 5] if family == "six_port" else [6, 5, 5]
        assert [length(alpha[central[i]]) for i in indices] == expected
        assert selected == {face_of[root], *(face_of[alpha[central[i]]] for i in indices)}
        vertices = frozenset(d[0] for i in selected for d in faces[i])
        old, ports, introduced = {"six_port": (12, 6, 4), "seven_port": (13, 7, 5),
                                  "eight_port": (14, 8, 2)}[family]
        assert len(vertices) == old
        assert sum(d[0] in vertices and d[1] not in vertices for d in alpha) == ports
        assert graph.subgraph(vertices).number_of_edges() == (3 * old - ports) // 2
        assert old > introduced
        cores[family, vertices] = selected
        occurrences.append(dict(dart=dart, family=family, recognized_root=root,
                                faces=sorted(selected), vertices=sorted(vertices)))
    # Independently scan each existing theorem's face mask. Several masks can
    # hold at one root, so each predicate must be considered independently.
    direct = set()
    for face in faces:
        n = len(face)
        lengths = [length(alpha[d]) for d in face]
        for i, root in enumerate(face):
            if n == 5 and all(lengths[(i + j) % n] == 5 for j in (1, 2, 3)):
                direct.add(("six_port", root))
            if [lengths[(i + j) % n] for j in (0, 1, -1)] == [6, 5, 5]:
                direct.add(("seven_port" if n == 5 else "eight_port", root))
    assert direct == {(r["family"], r["recognized_root"]) for r in occurrences}
    assert bool(flanked) == bool(cores)
    if not cores:
        assert max(counts) <= 2 and len(faces) >= 30 and len(graph) >= 56
    if len(graph) < 56:
        assert cores

    lobes, states = {}, 0
    for orbit in alternating_orbits(alpha, rho):
        for offset in range(len(orbit)):
            lobe = lobe_from(orbit, offset)
            key = tuple(sorted(tuple(sorted(d)) for d, _ in lobe))
            lobes.setdefault(key, lobe)
            states += 1
    assert states == 6 * len(graph)
    lobe_rows, coverage = [], Counter()
    for key, lobe in sorted(lobes.items()):
        detail = lobe_shores(graph, alpha, rho, faces, lobe)
        vertices, turns = detail["vertices"], detail["turns"]
        faults = [i for i in range(len(vertices)) if turns[i] == turns[(i + 1) % len(vertices)]]
        assert (len(faults) == 1 if len(vertices) % 2 else len(faults) in (0, 2))
        touches = [family for (family, core) in cores if core.intersection(vertices)]
        coverage["distinct_lobes"] += 1
        coverage["lobes_meeting_core"] += bool(touches)
        seam = None
        seam_cores = []
        if len(vertices) % 2:
            i = faults[0]
            seam = [vertices[i], vertices[(i + 1) % len(vertices)]]
            seam_cores = [family for family, core in cores if set(seam) <= core]
            coverage["odd_lobes"] += 1
            coverage["odd_seams_in_core"] += bool(seam_cores)
        lobe_rows.append(dict(vertices=vertices, dart_phase_segment=detail["dart_phase_segment"],
                              turns=turns, closing_faults=faults, seam=seam,
                              pentagon_shores=detail["pentagon_shores"],
                              intersecting_families=sorted(set(touches)),
                              seam_containing_families=sorted(set(seam_cores))))
    return dict(id=raw["id"], vertices=len(graph), faces=len(faces),
                rotation_sha256=hashlib.sha256(raw["rotation"].encode()).hexdigest(),
                neighbour_histogram=dict(sorted(Counter(counts).items())),
                pentagonal_incidences=sum(counts),
                flanked_darts=len(flanked),
                distinct_cores=dict(sorted(Counter(family for family, _ in cores).items())),
                occurrences_sha256=digest(occurrences),
                dart_phase_states=states, lobe_lengths=dict(sorted(Counter(map(len, lobes)).items())),
                closing_fault_histogram=dict(sorted(Counter(len(l["closing_faults"]) for l in lobe_rows).items())),
                coverage=dict(coverage), lobes_sha256=digest(lobe_rows),
                occurrences=occurrences, lobes=lobe_rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "alternating-lobe-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "diamond-supply-probe.json")
    args = parser.parse_args()
    if args.output.resolve() in {args.fixtures.resolve(), Path(__file__).resolve()}:
        parser.error("The output must not overwrite the input or program.")
    fixtures = json.loads(args.fixtures.read_text())["maps"]
    controls = [control(k) for k in (2, 3, 4)]
    results = [inspect(raw) for raw in fixtures + controls]
    assert all(r["coverage"].get("odd_lobes", 0) == r["coverage"].get("odd_seams_in_core", 0)
               for r in results[:len(fixtures)])
    first = next(r for r in results if r["flanked_darts"] and
                 r["coverage"]["lobes_meeting_core"] < r["coverage"]["distinct_lobes"])
    assert first["id"] == "C40-plantri-593"
    raw = next(r for r in fixtures if r["id"] == first["id"])
    witness = dict(id=first["id"], rotation=raw["rotation"],
                   occurrences=first["occurrences"],
                   disjoint_lobes=[l for l in first["lobes"] if not l["intersecting_families"]])
    regression = next(r for r in results if r["id"] == "C38-plantri-109")
    assert regression["distinct_cores"] == {"six_port": 6, "seven_port": 6}
    summary = dict(maps=len(results), maps_with_core=sum(bool(r["flanked_darts"]) for r in results),
                   maps_with_odd_lobes=sum(bool(r["coverage"].get("odd_lobes")) for r in results),
                   maps_with_core_containing_odd_seam=sum(bool(r["coverage"].get("odd_seams_in_core")) for r in results),
                   maps_without_core=[r["id"] for r in results if not r["flanked_darts"]],
                   totals=dict(sum((Counter(r["coverage"]) for r in results), Counter())))
    paths = [Path(__file__), args.fixtures,
             *(HERE / name for name in ("alternating_lobe_probe.py", "alternating_cycle_probe.py",
                                       "hexagonal_collar_probe.py")),
             *(HERE.parent / name for name in ("v24_goldberg.py", "v24_annular_census.py")),
             ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalNeighbourSupply.lean",
             ROOT / "lean/fourcolor-classical/MettapediaFourColor/DiamondGeometricSupply.lean"]
    report = dict(
        status="independent finite program evidence accompanying a separate Lean supply theorem",
        domain="Saved spherical cubic all-five/six rotations. Internal-six connectivity and minimality are not certified by this probe.",
        scope="All dart/phase starts and distinct first-return lobes, with no cycle-length cutoff.",
        observation="Incidence positions, not just distinct neighbouring faces.",
        source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        local_binary_words=local_words(), summary=summary,
        seam_observation="All 1489 odd closing seams in the 137 saved small maps lie in a recognized diamond core. This is finite evidence, not universal supply.",
        even_row_observation="One even alternating row is disjoint from every diamond core in its map. Row continuation or a different choice remains available; the controls have no diamond anywhere.",
        first_disjoint_row=witness,
        controls=[dict(**raw, result={k: v for k, v in r.items() if k not in ("occurrences", "lobes")},
                       first_lobe=r["lobes"][0])
                  for raw, r in zip(controls, results[len(fixtures):])],
        maps=[{k: v for k, v in r.items() if k not in ("occurrences", "lobes")} for r in results],
        remaining="Geometric supply for the residual larger all-five/six maps, other face sizes, and broader joint lobe reductions.")
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
