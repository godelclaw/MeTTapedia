"""Replay the shared-tip disk's cycle replacement and a physical repair test.

Geometry is checked in arbitrary contexts by separate Lean theorems. This
program checks concrete sewings, including disconnected exteriors, and all
258 proper colourings of one literal eight-cycle exterior. Its Kempe-orbit
calculation is program evidence, not a kernel proof of exterior closure or
of general geometric coverage.

Reference construction data and semantics come from Chris Emery's
MIT-licensed port; its licence and Gonthier/Werner and RSST attribution are
retained in lean/fourcolor-classical/LICENSE.
"""

from collections import Counter, deque
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import re
import sys

from mixed_diamond_reduction_probe import cycles, sew
from two_diamond_shared_tip_probe import canonical
from diamond_coloring_alternatives import colorings, support

ROOT = Path(__file__).resolve().parents[3]
CLASSICAL = ROOT / "lean/fourcolor-classical/MettapediaFourColor"

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def encoded(text, name):
    match = re.search(r"^def " + name + r" : String := (.*)$", text, re.M)
    assert match, name
    return [ord(c) - 33 for c in json.loads(match[1])]


def geometry(vertices, internal, ports, vertex, rho, alpha):
    assert Counter(vertex) == {v: 3 for v in range(vertices)}
    assert all(vertex[rho[d]] == vertex[d] for d in range(len(rho)))
    assert all(len(c) == 3 for c in cycles(rho))
    assert all(alpha[alpha[d]] == d != alpha[d] for d in range(internal))
    assert all(vertex[d] != vertex[alpha[d]] for d in range(internal))
    phi = [rho[alpha[d]] if d < internal else rho[d] for d in range(len(rho))]
    arcs = []
    for i in range(ports):
        d, arc = phi[internal+i], [internal+i]
        while d < internal:
            assert d not in arc
            arc.append(d)
            d = phi[d]
        arc.append(d)
        arcs.append(arc)
    faces = len(cycles(phi))
    return {"vertices": vertices, "internal": internal, "ports": ports,
            "vertex": vertex, "rho": rho, "alpha": alpha,
            "first_return_arcs": arcs, "open_faces": faces,
            "euler_mass": 2*vertices-internal+2*faces}


def source_piece():
    text = (CLASSICAL / "TwoDiamondTangle.lean").read_text()
    vertex, rho, alpha = [encoded(text, s) for s in
                          ("vertexCodes", "rotationCodes", "alphaCodes")]
    inverse = encoded(text, "inverseCodes")
    assert all(inverse[rho[d]] == d == rho[inverse[d]] for d in range(60))
    piece = geometry(20, 52, 8, vertex, rho, alpha)
    assert [len(a)-1 for a in piece["first_return_arcs"]] == [2, 3, 4, 3, 2, 3, 4, 3]
    assert all(a[-1] == 52+(i+1)%8 for i, a in enumerate(piece["first_return_arcs"]))
    match = re.search(r"^def original .*?lookupBase 33 (\"(?:[^\"\\]|\\.)*\")", text, re.M)
    original = [ord(c)-33 for c in json.loads(match[1])]
    table = (CLASSICAL / "TwoDiamondConfigurations.lean").read_text()
    table = table[table.index("def table003"):table.index("def vertex003")]
    edge, node = [[ord(c)-33 for c in json.loads(re.search(r"  "+s+r" := (.*)", table)[1])]
                  for s in ("edges", "nodes")]
    perimeter = {5, 0, 12, 53, 27, 22, 28, 11}
    assert set(original) == set(range(68))-perimeter and len(set(original)) == 60
    assert all(original[rho[d]] == node[original[d]] for d in range(60))
    assert all(original[alpha[d]] == edge[original[d]] for d in range(52))
    assert all(edge[original[52+i]] in perimeter for i in range(8))
    assert piece["open_faces"] == 8 and piece["euler_mass"] == 4
    return piece


def cycle_exterior(widths, reverse_ports=False):
    """Disjoint cycles, each with its literal cubic rotation and outward ports."""
    n = sum(widths)
    assert all(w >= 2 for w in widths)
    alpha = [d ^ 1 for d in range(2*n)]
    vertex, rho = [0]*(3*n), [0]*(3*n)
    offset = 0
    for width in widths:
        for j in range(width):
            i, previous, following = offset+j, offset+(j-1)%width, offset+(j+1)%width
            vertex[2*i], vertex[2*i+1], vertex[2*n+i] = i, previous, i
            rho[2*n+i], rho[2*i], rho[2*following+1] = 2*i, 2*following+1, 2*n+i
        offset += width
    if reverse_ports:
        assert len(widths) == 1
        change = list(range(2*n)) + [2*n+(-i)%n for i in range(n)]
        inv = [change.index(i) for i in range(3*n)]
        vertex = [vertex[change[d]] for d in range(3*n)]
        rho = [inv[rho[change[d]]] for d in range(3*n)]
    return geometry(n, 2*n, n, vertex, rho, alpha)


def exterior_word(a):
    return tuple(a[i] ^ a[(i+1)%8] for i in range(8))


def physical_moves(a):
    """Switch one genuine bichromatic component of the open exterior cycle."""
    word = exterior_word(a)
    for pair in ((1, 2), (1, 3), (2, 3)):
        graph = {v: set() for v in range(8)}
        for i in range(8):
            if a[i] in pair:
                graph[i].add((i-1)%8)
                graph[(i-1)%8].add(i)
        unseen = set(graph)
        while unseen:
            root = min(unseen)
            component, queue = {root}, [root]
            unseen.remove(root)
            for vertex in queue:
                for neighbor in sorted(graph[vertex]):
                    if neighbor in unseen:
                        unseen.remove(neighbor)
                        component.add(neighbor)
                        queue.append(neighbor)
            changed = tuple(pair[0] ^ pair[1] ^ c if i in component and c in pair else c
                            for i, c in enumerate(a))
            expected = tuple(pair[0] ^ pair[1] ^ c if i in component and c in pair else c
                             for i, c in enumerate(word))
            assert exterior_word(changed) == expected
            assert all(changed[i] != changed[(i+1)%8] for i in range(8))
            yield changed, {"pair": list(pair), "vertices": sorted(component)}


def repair_test():
    reference = ROOT / "lean/externals/fourcolor/FourColor/Configurations.lean"
    adj, boundary, _, _ = canonical(3, reference.read_text())
    vertices, witnesses = colorings(adj)
    good = support(vertices, witnesses, boundary)
    states = {a for a in product((1, 2, 3), repeat=8)
              if all(a[i] != a[(i+1)%8] for i in range(8))}
    accepted = {a for a in states if exterior_word(a) in good}
    distance, toward, queue = {a: 0 for a in accepted}, {}, deque(sorted(accepted))
    while queue:
        a = queue.popleft()
        for b, move in physical_moves(a):
            assert b in states
            if b not in distance:
                distance[b], toward[b] = distance[a]+1, (a, move)
                queue.append(b)
    assert set(distance) == states
    worst = min(a for a in states if distance[a] == max(distance.values()))
    a, path = worst, []
    while distance[a]:
        b, move = toward[a]
        assert any(c == b and operation == move for c, operation in physical_moves(a))
        path.append({"before": list(a), "operation": move, "after": list(b)})
        a = b
    assert exterior_word(a) in good
    witness = min(c for c in witnesses if tuple(c[boundary[i]] ^ c[boundary[(i+1)%8]]
                                              for i in range(8)) == exterior_word(a))
    return {"scope": "Literal eight-cycle exterior only; independent program evidence.",
            "proper_exterior_colourings": len(states), "directly_compatible": len(accepted),
            "distance_counts": {str(k): v for k, v in sorted(Counter(distance.values()).items())},
            "maximum_component_switches": max(distance.values()),
            "repaired_colourings": len(distance),
            "two_switch_example": {"initial": list(worst), "path": path,
                                   "compatible_face_colouring": list(witness)}}


def disconnected_tree_exterior_test(old, new):
    """A disconnected exterior survives even spherical girth-five geometry.

    This does not assert internal six-connectivity or the full normal form.
    The explicit graph prevents silently adding exterior connectivity as a
    consequence of the weaker source hypotheses.
    """
    witnesses = []
    tested = 0
    for signs in product((1, -1), repeat=4):
        vertex = [0, 1, 2, 3, 0, 1, 1, 0, 2, 3, 3, 2]
        rho, alpha = list(range(12)), [1, 0, 3, 2]
        for v, triple in enumerate(((0, 4, 7), (1, 5, 6), (2, 8, 11), (3, 9, 10))):
            for j, d in enumerate(triple):
                rho[d] = triple[(j+signs[v]) % 3]
        outside = geometry(4, 4, 8, vertex, rho, alpha)
        assert {(vertex[d], vertex[alpha[d]]) for d in (0, 2)} == {(0, 1), (2, 3)}
        for shift in range(8):
            tested += 1
            seam = [(i+shift) % 8 for i in range(8)]
            before, after = sew(outside, old, seam), sew(outside, new, seam)
            assert before["euler"] == after["euler"]
            assert before["vertices"] == after["vertices"]+12
            if before["euler"] != 2:
                continue
            vertices = vertex + [4+v for v in old["vertex"]]
            rotation = rho + [12+d for d in old["rho"]]
            flip = alpha + [-1]*8 + [12+d for d in old["alpha"]] + [-1]*8
            for i, j in enumerate(seam):
                flip[4+i], flip[64+j] = 64+j, 4+i
            faces = cycles([rotation[flip[d]] for d in range(72)])
            edges = [(vertices[d], vertices[flip[d]]) for d in range(72) if d < flip[d]]
            assert len({tuple(sorted(e)) for e in edges}) == len(edges) == 36
            assert all(u != v for u, v in edges)
            adj = [set() for _ in range(24)]
            for u, v in edges:
                adj[u].add(v)
                adj[v].add(u)
            assert all(len(ns) == 3 for ns in adj)
            girth = 25
            for u, v in edges:
                distance, queue = {u: 0}, [u]
                for w in queue:
                    for x in adj[w]:
                        if {w, x} == {u, v}:
                            continue
                        if x not in distance:
                            distance[x] = distance[w]+1
                            queue.append(x)
                girth = min(girth, distance.get(v, 24)+1)
            if girth >= 5:
                assert girth == 5
                assert sorted(map(len, faces)) == [5]*12+[6]*2
                witnesses.append({"signs": list(signs), "shift": shift,
                    "outside": outside, "seam": seam, "before": before, "after": after,
                    "girth": girth, "face_lengths": sorted(map(len, faces)),
                    "edges": [list(e) for e in edges]})
    assert tested == 128 and len(witnesses) == 2
    return {"scope": "Program counterexamples to exterior connectivity under spherical, simple, "
                     "cubic, bridgeless, girth-five hypotheses; full normal form is not asserted.",
            "orientation_and_seam_cases": tested, "witnesses": witnesses,
            "first_witness_small_cyclic_cuts": small_cyclic_cut_test(witnesses[0]["edges"], 24),
            "capped_exterior_potentials": capped_exterior_potential_test(witnesses[0])}


def capped_exterior_potential_test(witness):
    """Test exact flow/face transport through an eight-valent boundary hub.

    The hub is conserved, not properly Tait-coloured. All four remaining
    vertices retain their actual cubic colouring constraints.
    """
    outside, seam = witness["outside"], witness["seam"]
    rho = outside["rho"] + [12+(i+1) % 8 for i in range(8)]
    alpha = outside["alpha"] + [-1]*16
    for i, j in enumerate(seam):
        alpha[4+i], alpha[12+j] = 12+j, 4+i
    phi = [rho[alpha[d]] for d in range(20)]
    faces = cycles(phi)
    face_of = {d: f for f, ds in enumerate(faces) for d in ds}
    assert 5-10+len(faces) == 2
    cases = 0
    for first, second in product((1, 2, 3), repeat=2):
        for choices in product((0, 1), repeat=4):
            colour = [first, first, second, second] + [0]*16
            for v in range(4):
                ports = [d for d in range(4, 12) if outside["vertex"][d] == v]
                other = [c for c in (1, 2, 3) if c != colour[v]]
                for j, d in enumerate(ports):
                    colour[d] = other[j ^ choices[v]]
            for i in range(8):
                colour[12+i] = colour[alpha[12+i]]
            for orbit in cycles(rho):
                total = 0
                for d in orbit:
                    total ^= colour[d]
                assert total == 0
            neighbours = [[] for _ in faces]
            for d in range(20):
                assert colour[d] == colour[alpha[d]] != 0
                neighbours[face_of[d]].append((face_of[alpha[d]], colour[d]))
            potential, queue = {0: 0}, [0]
            for f in queue:
                for g, c in neighbours[f]:
                    if g not in potential:
                        potential[g] = potential[f] ^ c
                        queue.append(g)
                    assert potential[f] ^ potential[g] == c
            assert len(potential) == len(faces)
            k = [potential[face_of[d]] for d in range(20)]
            assert all(k[phi[d]] == k[d] for d in range(20))
            assert all(k[d] ^ k[alpha[d]] == colour[d] for d in range(20))
            # The mirrored reference node follows rho. Its ring trace is
            # exactly the physical word in the original positive port order.
            trace = [k[12+i] ^ k[rho[12+i]] for i in range(8)]
            assert trace == [colour[4+seam.index(i)] for i in range(8)]
            cases += 1
    assert cases == 144
    return {"evidence": "Independent bounded test of the proposed capped-remainder bridge.",
            "exterior_colourings": cases, "capped_vertices": 5, "capped_edges": 10,
            "capped_faces": len(faces), "hub_degree": 8,
            "exact_edge_and_ordered_trace_round_trips": cases}


def small_cyclic_cut_test(edges, n):
    """Enumerate every nontrivial vertex bipartition, fixing vertex 0 outside.

    This tests the two cut conditions of CubicDualInternallySixConnected,
    independently of Lean. Cycle detection allows disconnected shores.
    """
    adj = [0]*n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    assert all(ns.bit_count() == 3 for ns in adj)
    full = (1 << n)-1

    def cyclic(mask):
        unseen = mask
        while unseen:
            component = front = unseen & -unseen
            while front:
                bit = front & -front
                front ^= bit
                v = bit.bit_length()-1
                new = adj[v] & mask & ~component
                front |= new
                component |= new
            internal_edges = sum((adj[v] & component).bit_count()
                                 for v in range(n) if component >> v & 1)//2
            if internal_edges >= component.bit_count():
                return True
            unseen &= ~component
        return False

    mask = cut = 0
    counts = Counter()
    for i in range(1, 1 << (n-1)):
        bit = (i & -i) << 1
        v = bit.bit_length()-1
        delta = 3-2*(adj[v] & mask).bit_count()
        cut += -delta if mask & bit else delta
        mask ^= bit
        if cut <= 5 and cyclic(mask) and cyclic(full ^ mask):
            shore = min(mask.bit_count(), n-mask.bit_count())
            counts[(cut, shore)] += 1
            assert cut == 5 and shore <= 5, (mask, cut, shore)
    assert counts == {(5, 5): 12}
    return {"evidence": "Independent program check, not a kernel theorem or decoder bridge.",
            "vertex_bipartitions": (1 << (n-1))-1,
            "cyclic_cuts_of_size_at_most_four": 0,
            "cyclic_five_cuts": 12,
            "every_cyclic_five_cut_has_five_vertex_shore": True}


def run():
    old, new = source_piece(), cycle_exterior([8], reverse_ports=True)
    assert old["euler_mass"] == new["euler_mass"] == 4
    assert all(a[-1] == 16+(i+1)%8 for i, a in enumerate(new["first_return_arcs"]))
    cases = []
    for widths in ([8], [4, 4], [2, 6]):
        outside = cycle_exterior(widths)
        for sign in (1, -1):
            for shift in range(8):
                seam = [(sign*i+shift)%8 for i in range(8)]
                before, after = sew(outside, old, seam), sew(outside, new, seam)
                assert before["vertices"] == after["vertices"]+12
                assert before["euler"] == after["euler"]
                cases.append({"exterior_cycle_widths": widths, "sign": sign, "shift": shift,
                              "before": before, "after": after})
    one_cycle = [c for c in cases if c["exterior_cycle_widths"] == [8]]
    assert all(c["before"]["euler"] == (2 if c["sign"] == 1 else -4) for c in one_cycle)
    paths = [Path(__file__), CLASSICAL / "TwoDiamondTangle.lean",
             CLASSICAL / "TwoDiamondIntrinsic.lean", CLASSICAL / "TwoDiamondCycleReplacement.lean",
             CLASSICAL / "TwoDiamondConfigurations.lean", CLASSICAL / "TwoDiamondSplitRepair.lean",
             ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/CycleCapGeometry.lean",
             ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/CubicDualInternalSixConnectivity.lean",
             ROOT / "lean/externals/fourcolor/FourColor/Configurations.lean"]
    paths = sorted(set(paths) | {Path(module.__file__).resolve()
        for module in sys.modules.values() if getattr(module, "__file__", None)
        and Path(module.__file__).resolve().parent == Path(__file__).resolve().parent})
    return {"evidence": "Independent bounded program checks; kernel statements have their own audits.",
            "source_piece": {k: old[k] for k in
                             ("vertices", "internal", "ports", "first_return_arcs", "open_faces", "euler_mass")},
            "replacement_piece": {k: new[k] for k in
                                  ("vertices", "internal", "ports", "first_return_arcs", "open_faces", "euler_mass")},
            "sewings": cases, "literal_exterior_repair": repair_test(),
            "disconnected_tree_exteriors": disconnected_tree_exterior_test(old, new),
            "summary": {"seam_cases": len(cases),
                        "spherical_cases": sum(c["before"]["euler"] == 2 for c in cases),
                        "disconnected_spherical_cases": sum(c["before"]["euler"] == 2 and
                                                             len(c["exterior_cycle_widths"]) > 1 for c in cases),
                        "whole_map_vertex_decrease": 12},
            "source_sha256": {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in paths}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run()
    destination = args.output or Path(__file__).with_name("two-diamond-cycle-probe.json")
    assert destination.resolve() != Path(__file__).resolve()
    if args.check:
        assert report == json.loads(destination.read_text()), "Replay record differs."
    else:
        destination.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({**report["summary"], "exterior_repair": {
        k: report["literal_exterior_repair"][k] for k in
        ("proper_exterior_colourings", "directly_compatible", "distance_counts", "maximum_component_switches")}}))


if __name__ == "__main__":
    main()
