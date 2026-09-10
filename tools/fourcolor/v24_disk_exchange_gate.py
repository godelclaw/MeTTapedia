#!/usr/bin/env python3
"""A fixed-exterior obstruction to disk-local joint recolouring.

Preregistered question: does a disk containing both separated deletion sites
and the entire disagreement suffice for a strictly improving joint exchange
with the whole exterior fixed? Test unrestricted recolourings of that disk,
not only Kempe switches. Compare complete independent enumerators.

This is one planar reconfiguration control, not a ring-word catalogue or
reducibility checker. A positive minimum here is relative to the explicitly
frozen exterior, not an absolute minimum without boundary conditions.
"""

import argparse
import json
from pathlib import Path

from v24_absolute_topology_gate import enumerated
from v24_component_copy_gate import disagreement_components
from v24_deletion_orbit_gate import close, incidence
from v24_facial_bond_gate import component, face_dual_adjacency, validate
from v24_goldberg import edge_face_adjacency, make_goldberg_graph


def disk_data(graph, faces):
    """Check both facial sides and the full rim in this spherical map."""
    edges = list(map(tuple, graph['primal_edges']))
    dual = face_dual_adjacency(graph)
    sides = edge_face_adjacency(graph)
    other = set(range(len(dual))) - faces
    assert faces and other
    assert component(dual, faces, min(faces)) == faces
    assert component(dual, other, min(other)) == other
    rim = sorted(i for i, fs in sides.items() if len(set(fs) & faces) == 1)
    inner = sorted(i for i, fs in sides.items() if set(fs) <= faces)
    rim_adj = [set() for _ in range(graph['primal_vertex_count'])]
    for i in rim:
        u, v = edges[i]
        rim_adj[u].add(v)
        rim_adj[v].add(u)
    rim_vertices = {v for v, ns in enumerate(rim_adj) if ns}
    assert all(len(rim_adj[v]) == 2 for v in rim_vertices)
    assert component(rim_adj, rim_vertices, min(rim_vertices)) == rim_vertices
    cells = set(inner) | set(rim)
    vertices = {v for i in cells for v in edges[i]}
    assert len(vertices) - len(cells) + len(faces) == 1
    # Return the entire cyclic rim, not merely a convenient arc.
    rim_cycle = [min(rim_vertices)]
    previous, current = None, rim_cycle[0]
    while True:
        nxt = min(rim_adj[current] - {previous})
        if nxt == rim_cycle[0]:
            break
        assert nxt not in rim_cycle
        rim_cycle.append(nxt)
        previous, current = current, nxt
    assert set(rim_cycle) == rim_vertices
    return dict(faces=sorted(faces), complement_faces=sorted(other),
                interior_edges=inner, rim_edges=rim, rim_cycle=rim_cycle,
                frozen_edges=sorted(set(range(len(edges))) - set(inner)))


def run():
    graph = make_goldberg_graph(1)
    validate(graph, 2)
    n, edges = graph['primal_vertex_count'], list(map(tuple, graph['primal_edges']))
    source, target = {0, 1}, {17, 19}
    assert close(edges, source).isdisjoint(close(edges, target))
    disk = disk_data(graph, set(range(12)) - {6, 8})
    interior = set(disk['interior_edges'])
    assert all(i in interior for i, e in enumerate(edges) if set(e) & (source | target))
    frozen = disk['frozen_edges']
    assert frozen == [10, 11, 12, 13, 14, 17, 23, 25, 27]
    fixed = bytes([2, 0, 1, 0, 0, 2, 1, 1, 2])
    full = enumerated(n, edges)
    le = [e for e in edges if not set(e) & source]
    re = [e for e in edges if not set(e) & target]
    left, right = enumerated(n, le), enumerated(n, re)
    common = [e for e in le if e in re]
    li, ri = [le.index(e) for e in common], [re.index(e) for e in common]
    lf, rf = [le.index(edges[i]) for i in frozen], [re.index(edges[i]) for i in frozen]
    left_fiber = [c for c in left if bytes(c[i] for i in lf) == fixed]
    right_fiber = [c for c in right if bytes(c[i] for i in rf) == fixed]
    assert left_fiber and right_fiber, 'the exchange test is vacuous'
    full_fiber = [c for c in full if bytes(c[i] for i in frozen) == fixed]
    pairs = sorted((sum(c[i] != d[j] for i, j in zip(li, ri)), c, d)
                   for c in left_fiber for d in right_fiber)
    minimum = pairs[0][0]
    minimizing = []
    for delta, c, d in pairs:
        if delta != minimum:
            continue
        a, b = bytes(c[i] for i in li), bytes(d[i] for i in ri)
        parts = disagreement_components(n, common, a, b)
        assert all(edges.index(common[i]) in interior for part in parts for i in part)
        minimizing.append(dict(left=list(c), right=list(d),
            disagreement_edges=[edges.index(common[i]) for p in parts for i in p],
            components=[[edges.index(common[i]) for i in p] for p in parts]))
    # A full colouring changes the frozen exterior as little as possible.
    escaped = min(full, key=lambda c: (sum(c[i] != w for i, w in zip(frozen, fixed)), c))
    changes = [i for i, w in zip(frozen, fixed) if escaped[i] != w]
    # Check both one-face enlargements of the chosen disk, with their NEW
    # complete frozen boundaries. Each enlargement admits a common extension.
    enlargements = []
    for added in disk['complement_faces']:
        larger = disk_data(graph, set(disk['faces']) | {added})
        frozen_map = dict(zip(frozen, fixed))
        assert set(larger['frozen_edges']) <= set(frozen)
        extensions = [c for c in full if all(c[i] == frozen_map[i]
                      for i in larger['frozen_edges'])]
        enlargements.append(dict(added_face=added, disk=larger,
                                 full_extensions=len(extensions)))
    assert minimum > 0 and not full_fiber
    assert all(row['full_extensions'] for row in enlargements)
    return dict(schema='fourcolor-disk-exchange-control-v1',
        scope='one fixed exterior on one spherical dodecahedron; all deletion colourings',
        graph=dict(vertices=n, edges=edges, faces=graph['face_cycles'], stars=incidence(n, edges)),
        source=sorted(source), target=sorted(target), disk=disk, exterior_colors=list(fixed),
        complete_counts=dict(full=len(full), left=len(left), right=len(right)),
        frozen_counts=dict(full=len(full_fiber), left=len(left_fiber), right=len(right_fiber)),
        pair_count=len(pairs), frozen_minimum=minimum,
        all_minimizers=minimizing, unrestricted_minimum=0,
        full_coloring_with_smallest_exterior_change=list(escaped), exterior_change_edges=changes,
        larger_disks=enlargements)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(run()))
    if args.check:
        assert json.loads(args.check.read_text()) == result, 'receipt does not match replay'
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: result[key] for key in (
        'complete_counts', 'frozen_counts', 'pair_count', 'frozen_minimum',
        'unrestricted_minimum', 'exterior_change_edges')}, sort_keys=True))


if __name__ == '__main__':
    main()
