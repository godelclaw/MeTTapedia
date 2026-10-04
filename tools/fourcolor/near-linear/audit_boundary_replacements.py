#!/usr/bin/env python3
"""Test universal fixed-boundary replacements for four pinned patches.

This is independent program evidence. The six-port noncrossing-constraint
obstruction has a separate Lean proof; the larger searches do not. A rejected
replacement has a proper boundary colouring accepted by it but not by the
original patch. Exterior Kempe recolouring is outside this contract.
"""

import argparse
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate
from probe_pair_preparation import triangulations


def words(n):
    """Proper cycle words, one representative of each palette-renaming orbit."""
    def visit(w):
        if len(w) == n:
            if w[-1] != w[0]:
                yield tuple(w)
            return
        for c in range(min(3, max(w) + 1) + 1):
            if c != w[-1]:
                yield from visit(w + [c])
    yield from visit([0])


def profile(ring, patch):
    ws = list(words(ring))
    bad = 0
    for i, w in enumerate(ws):
        dfs = complete_patch(patch, w)
        ear, _ = eliminate(patch, ring, w)
        require((dfs is None) == (ear is None), 'DFS and exact ear elimination disagree')
        if dfs is None:
            bad |= 1 << i
    return ws, bad


def diagonals(ring):
    return {(a, b) for a in range(ring) for b in range(a + 2, ring)
            if (a, b) != (0, ring - 1)}


def face_edges(faces):
    return {tuple(sorted(e)) for a, b, c in faces for e in ((a, b), (a, c), (b, c))}


def mixed_constraints(ring, ws, bad):
    """Exhaust all equality patterns on every maximal noncrossing diagonal set.

Every partial conjunction extends to one of these complete patterns. Empty
domains are discarded, so inconsistency cannot masquerade as a replacement.
"""
    ds = diagonals(ring)
    allwords = (1 << len(ws)) - 1
    neq = {e: sum(1 << i for i, w in enumerate(ws) if w[e[0]] != w[e[1]]) for e in ds}
    winners, nodes, leaves = [], 0, 0
    for t, faces in enumerate(triangulations(0, ring - 1)):
        edges = sorted(face_edges(faces) & ds)
        require(len(edges) == ring - 3, 'Incomplete triangulation')
        def visit(i, domain, signs):
            nonlocal nodes, leaves
            nodes += 1
            if not domain:
                return
            if i == len(edges):
                leaves += 1
                if not domain & bad:
                    winners.append({'triangulation': t, 'signs': signs,
                                    'boundary_words': domain.bit_count()})
                return
            e = edges[i]
            visit(i + 1, domain & neq[e], signs + 'N')
            visit(i + 1, domain & (allwords ^ neq[e]), signs + 'E')
        visit(0, allwords, '')
    return {'triangulations': len(triangulations(0, ring - 1)),
            'recursion_nodes': nodes, 'feasible_complete_patterns': leaves,
            'successful_patterns': len(winners), 'first_success': winners[:1]}


def one_interior(ring, ws, bad):
    """Every triangulated disk with this simple ring and one interior vertex.

Choose its cyclic neighbours and triangulate each remaining polygonal gap.
The interior vertex extends precisely when its neighbours omit a colour.
"""
    badwords = [w for i, w in enumerate(ws) if bad >> i & 1]
    ds = diagonals(ring)
    masks = {e: sum(1 << i for i, w in enumerate(badwords) if w[e[0]] != w[e[1]])
             for e in ds}
    allbad = (1 << len(badwords)) - 1
    @lru_cache(None)
    def fillings(u, v):
        gap = [j % ring for j in range(u, v + 1)]
        out = []
        for fs in triangulations(0, len(gap) - 1):
            actual = tuple(tuple(gap[i] for i in face) for face in fs)
            edges = (face_edges(actual) | {tuple(sorted((u % ring, v % ring)))}) & ds
            domain = allbad
            for e in edges:
                domain &= masks[e]
            out.append((domain, edges))
        return out
    count, winners = 0, []
    for degree in range(3, ring + 1):
        for ns in combinations(range(ring), degree):
            centre = sum(1 << i for i, w in enumerate(badwords)
                         if len({w[v] for v in ns}) < 4)
            options = [fillings(u, v) for u, v in zip(ns, ns[1:] + (ns[0] + ring,))]
            for chosen in product(*options):
                count += 1
                domain = centre
                for mask, _ in chosen:
                    domain &= mask
                if domain:
                    continue
                edges = set().union(*(es for _, es in chosen))
                # A successful universal implication must have an actual input.
                witness = next((w for w in ws if len({w[v] for v in ns}) < 4 and
                                all(w[a] != w[b] for a, b in edges)), None)
                require(witness is not None, 'Vacuous one-vertex replacement')
                winners.append({'neighbours': ns, 'diagonals': sorted(edges),
                                'feasible_boundary': witness})
    return {'candidates': count, 'successful_candidates': len(winners),
            'first_success': winners[:1]}


def positive_control():
    # A hexagonal wheel with an extra vertex inside the triangle (0,1,6).
    # Removing that vertex is a strict reduction: a triangle omits a colour.
    adj = [set() for _ in range(8)]
    edges = {(v, (v + 1) % 6) for v in range(6)}
    edges |= {(v, 6) for v in range(6)} | {(7, v) for v in (0, 1, 6)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    ws, bad = profile(6, adj)
    result = one_interior(6, ws, bad)
    require(result['successful_candidates'] > 0, 'Search misses known strict reduction')
    for w in ws:
        if len(set(w)) < 4:
            require(complete_patch(adj, w) is not None, 'Wheel control failed reconstruction')
    return {'source_vertices': 8, 'replacement_vertices': 7,
            'fixed_boundary_reconstruction': True, 'search': result}


def lean_witnesses(here, ws, bad):
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/BoundaryReplacementObstruction.lean'
    text = lean.read_text()
    data = re.search(r'def wordData : String :=\s*"([0-3]+)"', text)[1]
    supplied = [tuple(map(int, data[i:i + 6])) for i in range(0, len(data), 6)]
    expected = [w for i, w in enumerate(ws) if bad >> i & 1]
    require(supplied == expected, 'Lean nonextension witnesses differ from independent profile')
    return {'witnesses': len(supplied), 'flat_witness_bytes': len(data),
            'module_sha256': sha256(lean.read_bytes()).hexdigest()}


def verify(here):
    cases = []
    lean = None
    expected = {'D0000': (31, 15, 14, 84), 'D0092': (7381, 6078, 4862, 75582),
                'D0063': (2461, 1839, 1430, 19448), 'D0099': (7381, 5794, 4862, 75582)}
    for name, counts in expected.items():
        raw = (here / (name + '.conf')).read_bytes()
        ring, patch = graph(raw)
        ws, bad = profile(ring, patch)
        mixed = mixed_constraints(ring, ws, bad)
        one = one_interior(ring, ws, bad)
        require((len(ws), bad.bit_count(), mixed['triangulations'], one['candidates']) == counts,
                'Replayed counts differ: ' + name)
        require(mixed['successful_patterns'] == one['successful_candidates'] == 0,
                'Candidate unexpectedly satisfies the reconstruction contract')
        cases.append({'source': name, 'source_sha256': sha256(raw).hexdigest(),
                      'ring': ring, 'core_vertices': len(patch) - ring,
                      'boundary_words': len(ws), 'nonextending_words': bad.bit_count(),
                      'mixed_noncrossing_constraints': mixed, 'one_interior_vertex': one})
        if name == 'D0000':
            lean = lean_witnesses(here, ws, bad)
    return {'evidence': 'Independent exhaustive program checks; separate Lean theorem only for D0000 noncrossing constraints.',
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'catalogue_attribution': 'Yuta Inoue, 2026, MIT licence; vendored source pins retained.',
            'contract': 'Every proper colouring of one fixed replacement reconstructs the source while fixing its whole boundary.',
            'extension_crosscheck': 'DFS agrees with exact two-port ear elimination on every canonical proper boundary word.',
            'cases': cases, 'lean_witness_crosscheck': lean, 'positive_control': positive_control(),
            'excluded_conclusions': ['No obstruction to exterior recolouring is proved.',
                                    'No assertion of impossibility of compositional proofs.',
                                    'No claim about all smaller gadgets or stronger ambient hypotheses.'],
            'catalogue_entries_removed': 0, 'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
