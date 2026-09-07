#!/usr/bin/env python3
"""Exact ordering gate for the repaired ambient mesh-cell regions.

Population: all inter-contour bands in the eight existing GP(k,0) receipts.
Candidate bound: the larger of the widest filled singleton cell and the
filled full band suffices for every intermediate cut after reordering.

Search the complete subset lattice of cells. Each nonempty state must be
face-connected; its full vertex side is filled relative to the same anchor.
Only strictly growing hull steps are allowed. The bottleneck recurrence is
checked against all permutations for the bands with at most six cells
and for the eight-cell GP(3,0) obstruction.
This is optimality within this fixed geometric candidate family only.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import verify_archive
from v24_mesh_region_gate import audit as audit_regions, components, vertex_data
from v24_goldberg import edge_face_adjacency


def bits(values):
    return sum(1 << v for v in set(values))


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def flood(adjacency, allowed, root):
    assert allowed & (1 << root)
    seen, frontier = 0, 1 << root
    while frontier:
        seen |= frontier
        nxt = 0
        for v in members(frontier):
            nxt |= adjacency[v]
        frontier = nxt & allowed & ~seen
    return seen


def bottleneck(costs, hulls):
    """None is an invalid state or an unreachable state, never zero cost."""
    best, parent = [None] * len(costs), [None] * len(costs)
    best[0] = 0
    for state in range(1, len(costs)):
        if costs[state] is None:
            continue
        candidates = []
        for last in members(state):
            old = state ^ (1 << last)
            if best[old] is not None and hulls[old] != hulls[state]:
                assert hulls[old] & ~hulls[state] == 0
                candidates.append((max(best[old], costs[state]), old))
        if candidates:
            best[state], parent[state] = min(candidates)
    return best, parent


def brute_force(costs, hulls, n):
    best = None
    for order in itertools.permutations(range(n)):
        state, peak = 0, 0
        for cell in order:
            new = state | (1 << cell)
            if costs[new] is None or hulls[state] == hulls[new]:
                break
            peak = max(peak, costs[new])
            state = new
        else:
            best = peak if best is None else min(best, peak)
    return best


def inspect(graph, region, band, full_brute=False):
    edges, faces = graph['primal_edges'], graph['face_cycles']
    nvertices = graph['primal_vertex_count']
    universe = (1 << nvertices) - 1
    adjacency = [0] * nvertices
    for u, v in edges:
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u
    ids, anchor = band['cells'], band['anchor']
    assert anchor is not None
    cells = [set(region['cells'][i]['faces']) for i in ids]
    cell_of = {f: i for i, cell in enumerate(cells) for f in cell}
    assert sum(map(len, cells)) == len(cell_of)
    n = len(cells)
    cell_adj = [set() for _ in cells]
    for f, g in edge_face_adjacency(graph).values():
        if f in cell_of and g in cell_of and cell_of[f] != cell_of[g]:
            cell_adj[cell_of[f]].add(cell_of[g])
            cell_adj[cell_of[g]].add(cell_of[f])
    raw = [0] * (1 << n)
    hulls = [0] * (1 << n)
    costs = [None] * (1 << n)
    costs[0] = 0
    cell_vertices = [bits(v for f in cell for v in faces[f]) for cell in cells]
    for state in range(1, 1 << n):
        bit = state & -state
        raw[state] = raw[state ^ bit] | cell_vertices[bit.bit_length() - 1]
        hulls[state] = universe ^ flood(adjacency, universe ^ raw[state], anchor)
        if len(components(cell_adj, set(members(state)))) != 1:
            continue
        side = set(members(hulls[state]))
        data = vertex_data(graph, side)
        assert data['both_connected'] and data['both_cyclic'] and data['order'] is not None
        assert data['inside_majority']
        assert any(anchor in face and set(face).isdisjoint(side) for face in faces)
        costs[state] = data['width']
    best, parent = bottleneck(costs, hulls)
    brute_checked = n <= 6 or full_brute
    if brute_checked:
        assert best[-1] == brute_force(costs, hulls, n)
    assert best[-1] is not None
    path, state = [], (1 << n) - 1
    while state:
        old = parent[state]
        path.append(dict(cell=ids[(state ^ old).bit_length() - 1], state=state,
                         faces=sorted(set().union(*(cells[i] for i in members(state)))),
                         **vertex_data(graph, set(members(hulls[state])))))
        state = old
    path.reverse()
    local_bound = max(costs[1 << i] for i in range(n))
    candidate = max(local_bound, costs[-1])
    level_bounds = []
    for size in range(1, n + 1):
        states = [s for s in range(1, 1 << n) if s.bit_count() == size and best[s] is not None]
        level_bounds.append(min(best[s] for s in states) if states else None)
    return dict(rows=band['rows'], cell_ids=ids, anchor=anchor,
                costs=costs, best=best, parent=parent,
                strict_transitions=[[s ^ (1 << i), s] for s in range(1, 1 << n) for i in members(s)
                                    if hulls[s ^ (1 << i)] != hulls[s]],
                candidate_bound=candidate, optimum=best[-1], full_width=costs[-1],
                prefix_level_bounds=level_bounds,
                bfs_peak=max(s['saturation']['width'] for s in band['sequence']),
                optimum_path=path, brute_force_checked=brute_checked)


def audit(archive, regions, orders):
    verify_archive(archive)
    assert regions == audit_regions(archive, orders)
    assert len(archive['receipts']) == len(regions['receipts']) == 8
    assert [r['frequency'] for r in archive['receipts']] == list(range(1, 9))
    records, summaries = [], []
    for original, region in zip(archive['receipts'], regions['receipts']):
        assert original['frequency'] == region['frequency']
        bands = [inspect(original['graph'], region, b,
                         original['frequency'] == 3 and b['rows'] == [3, 4])
                 for b in region['bands']]
        records.append(dict(frequency=original['frequency'], bands=bands))
        summaries.append(dict(frequency=original['frequency'], bands=len(bands),
            counterexamples=sum(b['optimum'] > b['candidate_bound'] for b in bands),
            max_bfs=max(b['bfs_peak'] for b in bands), max_optimum=max(b['optimum'] for b in bands),
            max_candidate=max(b['candidate_bound'] for b in bands),
            brute_force_checks=sum(b['brute_force_checked'] for b in bands)))
    return dict(schema='fourcolor-v24-mesh-region-order-v1', summaries=summaries, receipts=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = audit(json.loads(Path('results/fourcolor/v24_contour_mesh_gate.json').read_text()),
                   json.loads(Path('results/fourcolor/v24_mesh_region_gate.json').read_text()),
                   json.loads(Path('results/fourcolor/v24_ordered_contour_gate.json').read_text()))
    if args.output:
        atomic_write_json(args.output, result)
    if args.check:
        assert result == json.loads(args.check.read_text())
    print(json.dumps(result['summaries'], indent=2))
