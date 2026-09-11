#!/usr/bin/env python3
"""Gate for topology rejection in the physical compositional evaluator.

Preregistered outcomes:
* Euler defect grows by two precisely on a same-component/different-face
  edge insertion, using rho(a), rho(b) in the prepend convention.
* A realized nonempty zero-cut record with no selected port is equivalent
  to an invisible component. It forbids connected gluing to a nonempty
  exterior, but need not forbid accepting the already closed object.

These are generic permutation and graph controls, not a census of
counterexamples or a reducibility catalogue. All transposition words up
to length three on at most four darts are tested, including repetitions.
All simple graphs on at most four vertices and port lists of length at
most two are tested. No four-colour theorem or planarity filter is used.
"""

from collections import Counter
from itertools import combinations, permutations, product
import json


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def swap(n, a, b):
    p = list(range(n))
    p[a], p[b] = b, a
    return tuple(p)


def orbit_labels(p):
    labels = [-1] * len(p)
    count = 0
    for start in range(len(p)):
        if labels[start] >= 0:
            continue
        at = start
        while labels[at] < 0:
            labels[at] = count
            at = p[at]
        assert at == start
        count += 1
    return labels, count


def component_labels(n, edges):
    """Union-find, independent of the face-permutation traversal."""
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for a, b in edges:
        parent[find(a)] = find(b)
    return tuple(find(v) for v in range(n))


def presentation(rho, edges):
    beta = tuple(range(len(rho)))
    for a, b in reversed(edges):
        beta = compose(swap(len(rho), a, b), beta)
    phi = compose(rho, beta)
    faces, face_count = orbit_labels(phi)
    _, vertices = orbit_labels(rho)
    comps = component_labels(len(rho), tuple(enumerate(rho)) + edges)
    defect = len(edges) + 2 * len(set(comps)) - vertices - face_count
    return comps, faces, defect


def edge_gate():
    increments = Counter()
    misplaced_face_test = None
    checked = 0
    for n in range(5):
        options = tuple(combinations(range(n), 2))
        for rho in permutations(range(n)):
            assert presentation(rho, ())[2] == 0
            for size in range(4):
                for edges in product(options, repeat=size):
                    comps, faces, defect = presentation(rho, edges)
                    assert defect >= 0 and defect % 2 == 0
                    for a, b in options:
                        new_comps, _, new_defect = presentation(rho, ((a, b),) + edges)
                        connected = comps[a] == comps[b]
                        same_face = faces[rho[a]] == faces[rho[b]]
                        assert not same_face or connected
                        assert len(set(comps)) - len(set(new_comps)) == int(not connected)
                        expected = 2 * int(connected and not same_face)
                        assert new_defect - defect == expected
                        increments[expected] += 1
                        checked += 1
                        wrong = 2 * int(connected and faces[a] != faces[b])
                        # For physical insertion at unused darts the unrotated
                        # coordinates are equivalent. Do not claim this control
                        # refutes that stronger-hypothesis version.
                        if all(a not in e and b not in e for e in edges):
                            assert wrong == expected
                        if wrong != expected and misplaced_face_test is None:
                            misplaced_face_test = dict(rho=rho, edges=edges, added=(a, b),
                                                       actual=expected, wrong=wrong)
    assert misplaced_face_test is not None
    return dict(checked=checked, increments=dict(sorted(increments.items())),
                wrong_face_coordinates_refuted=misplaced_face_test)


def hidden_by_cut(n, edges, ports):
    for mask in range(1, 1 << n):
        bit = lambda v: (mask >> v) & 1
        if not any(bit(p) for p in ports) and all(bit(a) == bit(b) for a, b in edges):
            return mask
    return None


def visibility_gate():
    checked = hidden = sewn = 0
    for n in range(5):
        options = tuple(combinations(range(n), 2))
        for chosen in range(1 << len(options)):
            edges = tuple(e for i, e in enumerate(options) if (chosen >> i) & 1)
            comps = component_labels(n, edges)
            for width in range(3):
                for ports in product(range(n), repeat=width):
                    witness = hidden_by_cut(n, edges, ports)
                    visible = all(c in {comps[p] for p in ports} for c in comps)
                    assert (witness is None) == visible
                    checked += 1
                    if witness is None:
                        continue
                    hidden += 1
                    # Two-vertex exteriors, isolated or joined, and every port map.
                    # The proof target is arbitrary nonempty exteriors, not this sample.
                    for other_edges in ((), ((n, n + 1),)):
                        for other_ports in product(range(n, n + 2), repeat=width):
                            joined = component_labels(n + 2, edges + other_edges
                                                      + tuple(zip(ports, other_ports)))
                            assert len(set(joined)) > 1
                            sewn += 1
    # A finished connected closed object has a hidden component. Blind rejection
    # would lose valid final objects; the continuation must add a nonempty exterior.
    assert hidden_by_cut(2, ((0, 1),), ()) is not None
    assert len(set(component_labels(2, ((0, 1),)))) == 1
    assert hidden_by_cut(0, (), ()) is None
    return dict(checked=checked, hidden=hidden, nonempty_exterior_checks=sewn,
                reject_closed_finished_object_is_unsound=True,
                empty_initial_object_has_no_hidden_record=True)


def run():
    from v24_joint_vertex_step_gate import bounded_closure
    return dict(scope="generic edge presentations and small graph gluing; not a Lean certificate",
                edge_insertion=edge_gate(), visibility=visibility_gate(),
                width3_viable_closure=bounded_closure(3, prune_hidden=True))


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
