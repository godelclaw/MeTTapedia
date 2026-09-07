#!/usr/bin/env python3
"""Embedded mesh-cell repair using full ambient face components.

Preregistered population: the eight existing GP(k,0) contour/linkage receipts.
Keep every selected contour edge and linkage edge, then compute components
of the ambient face dual with crossings of those barrier edges forbidden.
Their boundaries, not designated branch corners, are the candidate cells.

Reject non-simple full cell boundaries. Check the entire closed vertex side,
its complement, its boundary order, and inside-majority. For each inter-row
band, grow cumulative unions in a deterministic connected cell order and
record complete interfaces; local boundary size is not a corridor theorem.
No colouring enumeration or target non-colourability assumption is used.
"""

import argparse
import json
from collections import deque
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import cycle_order, verify_archive
from v24_geodesic_mincut_gate import boundary_order, connected
from v24_goldberg import edge_face_adjacency


def components(adjacency, allowed):
    todo = set(allowed)
    result = []
    while todo:
        seen, queue = {min(todo)}, deque([min(todo)])
        while queue:
            u = queue.popleft()
            for v in sorted(adjacency[u]):
                if v in todo and v not in seen:
                    seen.add(v)
                    queue.append(v)
        result.append(seen)
        todo -= seen
    return result


def vertex_data(graph, side):
    edges = graph['primal_edges']
    n = graph['primal_vertex_count']
    outside = set(range(n)) - side
    cut = [e for e, (u, v) in enumerate(edges) if (u in side) != (v in side)]
    inner = [e for e in edges if set(e) <= side]
    outer = [e for e in edges if set(e) <= outside]
    both_connected = connected(n, edges, side) and connected(n, edges, outside)
    order = None
    if both_connected:
        try:
            order, _ = boundary_order(edge_face_adjacency(graph), cut)
        except AssertionError:
            pass
    return dict(vertices=sorted(side), width=len(cut), cut=cut, order=order,
                both_connected=both_connected,
                both_cyclic=both_connected and len(inner) >= len(side) and len(outer) >= len(outside),
                inside_majority=all(sum(v in e for e in inner) >= 2 for v in side))


def side_data(graph, face_ids):
    return vertex_data(graph, {v for f in face_ids for v in graph['face_cycles'][f]})


def inspect(receipt, order):
    graph = receipt['graph']
    edges = graph['primal_edges']
    edge_ids = {tuple(sorted(e)): i for i, e in enumerate(edges)}
    lo, hi = receipt['selected']
    contours = receipt['contours'][lo:hi + 1]
    assert len(contours) >= 2
    selected = order['selected_columns']
    assert len(selected) >= 2 and len(set(selected)) == len(selected)
    assert all(type(j) is int and 0 <= j < len(receipt['paths']) for j in selected)
    row_edges = [{edge_ids[tuple(sorted(e))] for e in zip(r['cycle'], r['cycle'][1:] + r['cycle'][:1])}
                 for r in contours]
    columns = [receipt['paths'][j] for j in order['selected_columns']]
    barrier = set.union(*row_edges) | {edge_ids[tuple(sorted(e))] for p in columns for e in zip(p, p[1:])}
    edge_faces = edge_face_adjacency(graph)
    adjacency = [set() for _ in graph['face_cycles']]
    full_dual = [set() for _ in graph['face_cycles']]
    for e, (f, g) in edge_faces.items():
        full_dual[f].add(g)
        full_dual[g].add(f)
        if e not in barrier:
            adjacency[f].add(g)
            adjacency[g].add(f)
    cells = components(adjacency, range(len(adjacency)))
    cell_of = {f: i for i, cell in enumerate(cells) for f in cell}
    cell_adj = [set() for _ in cells]
    all_boundary = set()
    records = []
    for i, cell in enumerate(cells):
        cut = [e for e, (f, g) in edge_faces.items() if (f in cell) != (g in cell)]
        assert set(cut) <= barrier
        all_boundary.update(cut)
        try:
            boundary = cycle_order(edges, cut)
        except (AssertionError, ValueError):
            boundary = None
        records.append(dict(faces=sorted(cell), boundary=boundary,
                            complement_dual_connected=len(components(full_dual, set(range(len(adjacency))) - cell)) == 1,
                            touching_rows=[j for j, row in enumerate(row_edges) if row & set(cut)],
                            side=side_data(graph, cell)))
    for f, g in edge_faces.values():
        if cell_of[f] != cell_of[g]:
            cell_adj[cell_of[f]].add(cell_of[g])
            cell_adj[cell_of[g]].add(cell_of[f])
    bands = []
    primal_adj = [set() for _ in range(graph['primal_vertex_count'])]
    for u, v in edges:
        primal_adj[u].add(v)
        primal_adj[v].add(u)
    for j in range(len(contours) - 1):
        region = set(contours[j]['faces']) - set(contours[j + 1]['faces'])
        chosen = {i for i, cell in enumerate(cells) if cell <= region}
        assert set().union(*(cells[i] for i in chosen)) == region
        parts = components(cell_adj, chosen)
        assert len(parts) == 1
        todo = set(chosen)
        queue, seen, prefix, sequence = deque([min(todo)]), {min(todo)}, set(), []
        band_vertices = {v for f in region for v in graph['face_cycles'][f]}
        anchors = set(range(len(primal_adj))) - band_vertices
        anchor = min(anchors) if anchors else None
        previous = set()
        previous_filled = set()
        while queue:
            i = queue.popleft()
            prefix |= cells[i]
            data = side_data(graph, prefix)
            vertices = set(data['vertices'])
            data['strict_vertex_growth'] = previous < vertices
            previous = vertices
            data['faces'] = sorted(prefix)
            data['face_complement_connected'] = len(components(full_dual, set(range(len(full_dual))) - prefix)) == 1
            data['anchor_face'] = next((f for f, cycle in enumerate(graph['face_cycles'])
                                       if anchor in cycle and vertices.isdisjoint(cycle)), None)
            if anchor is not None:
                outside = next(part for part in components(primal_adj, set(range(len(primal_adj))) - vertices)
                               if anchor in part)
                filled = set(range(len(primal_adj))) - outside
                saturation = vertex_data(graph, filled)
                assert previous_filled <= filled and set(saturation['cut']) <= set(data['cut'])
                saturation['strict_vertex_growth'] = previous_filled < filled
                saturation['fresh_exterior_vertices'] = sorted(vertices - previous_filled)
                assert saturation['strict_vertex_growth'] == bool(saturation['fresh_exterior_vertices'])
                if data['anchor_face'] is not None:
                    assert filled.isdisjoint(graph['face_cycles'][data['anchor_face']])
                previous_filled = filled
                data['saturation'] = saturation
            sequence.append(dict(cell=i, **data))
            for nxt in sorted(cell_adj[i] & chosen):
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        assert seen == chosen
        bands.append(dict(rows=[j, j + 1], cells=sorted(chosen), anchor=anchor, sequence=sequence))
    return dict(frequency=receipt['frequency'], barrier=sorted(barrier),
                unused_barrier_edges=sorted(barrier - all_boundary), cells=records, bands=bands)


def audit(archive, orders):
    verify_archive(archive)
    assert len(archive['receipts']) == len(orders['spheres']) == 8
    assert [r['frequency'] for r in archive['receipts']] == list(range(1, 9))
    results = []
    for receipt, order in zip(archive['receipts'], orders['spheres']):
        assert receipt['frequency'] == order['frequency']
        results.append(inspect(receipt, order))
    summaries = []
    for result in results:
        prefixes = [s for b in result['bands'] for s in b['sequence']]
        filled = [s['saturation'] for s in prefixes if 'saturation' in s]
        summaries.append(dict(frequency=result['frequency'], cells=len(result['cells']),
            nonsimple=sum(c['boundary'] is None for c in result['cells']),
            unused_barrier=len(result['unused_barrier_edges']),
            max_cell_width=max(c['side']['width'] for c in result['cells']),
            max_band_prefix_width=max(p['width'] for p in prefixes),
            bad_prefix_connectivity=sum(not p['both_connected'] for p in prefixes),
            bad_prefix_cyclicity=sum(not p['both_cyclic'] for p in prefixes),
            bad_prefix_strictness=sum(not p['strict_vertex_growth'] for p in prefixes),
            saturated_prefixes=len(filled),
            saturated_max_width=max(p['width'] for p in filled),
            saturated_bad_connectivity=sum(not p['both_connected'] for p in filled),
            saturated_bad_cyclicity=sum(not p['both_cyclic'] for p in filled),
            saturated_missing_order=sum(p['order'] is None for p in filled),
            prefixes_with_anchor_face=sum(p['anchor_face'] is not None for p in prefixes),
            saturated_nonstrict_steps=sum(not p['strict_vertex_growth'] for p in filled)))
    return dict(schema='fourcolor-v24-mesh-region-v1', summaries=summaries, receipts=results)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path, help='replay and compare a complete stored receipt')
    args = parser.parse_args()
    result = audit(json.loads(Path('results/fourcolor/v24_contour_mesh_gate.json').read_text()),
                   json.loads(Path('results/fourcolor/v24_ordered_contour_gate.json').read_text()))
    if args.output:
        atomic_write_json(args.output, result)
    if args.check:
        assert json.loads(args.check.read_text()) == result, 'stored region receipt differs from replay'
    print(json.dumps(result['summaries'], indent=2))
