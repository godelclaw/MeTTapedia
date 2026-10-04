#!/usr/bin/env python3
"""Test joint anchor propagation against exact elimination on three sources.

Every successful guard is reconstructed into a full source colouring. Only
aggregate results are saved. This program evidence does not replace the Lean
forest theorem or establish a universal four-sweep bound or reducibility.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, traces


PINS = {
    'D0092': 'cc8286c01ce19b57b793a4eb1b28633d66cd210ea2a313dd0ba3e7d07231ea14',
    'D0063': 'd231a65aabea1df62b0d319999ec656d350f3da43a35d6f7db79274af7bebf8d',
    'D0099': '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
}


def supported(lists, edges):
    return all(any(a != b for b in lists[v]) for u, v in edges for a in lists[u])


def propagate(initial, anchors, choice, edges):
    lists = [set(s) for s in initial]
    for v, a in zip(anchors, choice):
        lists[v] &= {a}
    # A changed sweep removes at least one of the initially retained colours.
    for count in range(1, sum(map(len, lists)) + 2):
        before = [set(s) for s in lists]
        for v, u in edges:
            lists[u] = {a for a in lists[u] if any(a != b for b in lists[v])}
        if any(not s for s in lists):
            return None, count
        if before == lists:
            require(supported(lists, edges), 'Fixed point lacks support')
            return lists, count
    raise AssertionError('Propagation exceeded the strict deletion bound')


def reconstruct(g, ring, b, anchors, choice, lists):
    """Greedily colour each residual tree after jointly fixing both anchors."""
    colours = dict(zip(anchors, choice))
    for root in range(len(lists)):
        if root in colours:
            continue
        colours[root] = min(lists[root])
        todo = [root]
        while todo:
            v = todo.pop()
            for ambient_u in sorted(g[ring + v]):
                u = ambient_u - ring
                if u < 0 or u in colours:
                    continue
                options = lists[u] - {colours[v]}
                require(bool(options), 'Missing tree-edge support')
                colours[u] = min(options)
                todo.append(u)
    full = list(b) + [colours[i] for i in range(len(lists))]
    require(all(full[v] != full[u] for v in range(len(g)) for u in g[v]),
            'Reconstructed full source colouring violates an edge')
    require(all(colours[v] in lists[v] for v in colours), 'Reconstruction left a list')


def verify(here):
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/TriangleStripLists.lean'
    block = lean.read_text().split('def anchorAt', 1)[1].split('theorem anchor_cover', 1)[0]
    anchors = {name.upper(): tuple(map(int, pair.split(',')))
               for name, pair in re.findall(r'\| \.(d\d+) => \(!\[([0-9,]+)\]', block)}
    require(set(anchors) == set(PINS), 'Lean anchor sources differ')
    rows = []
    for name, digest in PINS.items():
        raw = (here / (name + '.conf')).read_bytes()
        require(sha256(raw).hexdigest() == digest, 'Source pin differs')
        ring, g = graph(raw)
        n = len(g) - ring
        pair = anchors[name]
        require(len(pair) == 2 and len(set(pair)) == 2, 'Anchor arity differs')
        edges = [(v, u) for v in range(n) for u in range(n) if u + ring in g[v + ring]]
        remaining = set(range(n)) - set(pair)
        visited = set()

        def visit(v, parent):
            require(v not in visited, 'Anchors leave a cycle')
            visited.add(v)
            for u in sorted(remaining):
                if (v, u) in edges and u != parent:
                    visit(u, v)

        for v in sorted(remaining):
            if v not in visited:
                visit(v, None)
        counts = Counter(inputs=0, colourable=0, successful_anchor_assignments=0)
        max_sweeps = 0
        for word in traces(ring):
            b = boundary(word)
            exact = eliminate(g, ring, b)[0] is not None
            initial = [set(range(4)) - {b[u] for u in g[v] if u < ring}
                       for v in range(ring, len(g))]
            success = 0
            for choice in product(range(4), repeat=2):
                residual, sweeps = propagate(initial, pair, choice, edges)
                max_sweeps = max(max_sweeps, sweeps)
                if residual is not None:
                    reconstruct(g, ring, b, pair, choice, residual)
                    success += 1
            require(bool(success) == exact, f'Propagation/elimination mismatch: {name} {word}')
            counts['inputs'] += 1
            counts['colourable'] += exact
            counts['successful_anchor_assignments'] += success
        rows.append(dict(source=name, source_sha256=digest, ring=ring, core=n,
                         anchors=pair, joint_choices_per_input=16,
                         maximum_observed_sweeps=max_sweeps, **counts))
    return dict(classification='BOUNDED_PROGRAM_CROSSCHECK', sources=rows,
                total_inputs=sum(r['inputs'] for r in rows),
                total_reconstructions=sum(r['successful_anchor_assignments'] for r in rows),
                lean_anchor_source_sha256=sha256(lean.read_bytes()).hexdigest(),
                universal_four_sweep_bound_claimed=False,
                reducibility_claimed=False, coverage_entries_removed=0,
                original_certificate_dependencies_removed=0,
                all_boundary_table_exported=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
