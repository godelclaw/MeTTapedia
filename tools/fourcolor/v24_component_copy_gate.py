#!/usr/bin/env python3
"""Whole-disagreement-component exchange: a structural, non-catalogue gate.

Preregistered outcomes: boundary-avoiding copies preserve properness and
remove exactly the copied disagreements; omitting the boundary condition
admits a counterexample. All colourings of the selected deletion graphs
are exhausted, cross-checked independently, with no enumeration cap.
These are ordinary colourable controls, not least counterexamples.
"""
from collections import Counter
import json

from v24_deletion_orbit_gate import (
    make_goldberg_graph, validate, colorings, vertex_colorings, incidence, close,
)


def disagreement_components(n, edges, left, right):
    inc = incidence(n, edges)
    unseen = {i for i in range(len(edges)) if left[i] != right[i]}
    result = []
    while unseen:
        part, stack = set(), [min(unseen)]
        while stack:
            i = stack.pop()
            if i in part:
                continue
            part.add(i)
            stack.extend(j for v in edges[i] for j in inc[v]
                         if j in unseen and j not in part)
        unseen -= part
        result.append(sorted(part))
    return result


def proper(n, edges, colors):
    return all(len({colors[i] for i in star}) == len(star)
               for star in incidence(n, edges))


def copied(old, donor, image, part):
    result = bytearray(old)
    for i in part:
        result[image[i]] = donor[i]
    return bytes(result)


def run():
    graph = make_goldberg_graph(1)
    validate(graph, 2)
    n, edges = graph['primal_vertex_count'], list(map(tuple, graph['primal_edges']))
    A, B = {0, 1}, {17, 19}
    assert close(edges, A).isdisjoint(close(edges, B))
    left_edges = [e for e in edges if not set(e) & A]
    right_edges = [e for e in edges if not set(e) & B]
    common = [e for e in edges if not set(e) & (A | B)]
    lc, rc = colorings(n, left_edges), colorings(n, right_edges)
    assert lc == vertex_colorings(n, left_edges)
    assert rc == vertex_colorings(n, right_edges)
    li, ri = [left_edges.index(e) for e in common], [right_edges.index(e) for e in common]
    totals, unsafe = Counter(), None
    for left in lc:
        for right in rc:
            totals['coloring_pairs'] += 1
            cl, cr = bytes(left[i] for i in li), bytes(right[i] for i in ri)
            before = sum(a != b for a, b in zip(cl, cr))
            for part in disagreement_components(n, common, cl, cr):
                totals['disagreement_components'] += 1
                vertices = {v for i in part for v in common[i]}
                for old, donor, image, ambient, forbidden in (
                    (left, cr, li, left_edges, close(edges, B) - B),
                    (right, cl, ri, right_edges, close(edges, A) - A),
                ):
                    new = copied(old, donor, image, part)
                    if not vertices & forbidden:
                        assert proper(n, ambient, new)
                        after = sum(new[image[i]] != donor[i] for i in range(len(common)))
                        assert after == before - len(part)
                        totals['valid_decreasing_copies'] += 1
                    elif not proper(n, ambient, new):
                        totals['invalid_copies_without_boundary_condition'] += 1
                        if unsafe is None:
                            unsafe = dict(edges=ambient, common=common, old=list(old),
                                          donor=list(donor), image=image, component=part,
                                          copied=list(new), forbidden_ports=sorted(forbidden))
    assert totals['valid_decreasing_copies'] > 0, 'exchange check was vacuous'
    assert unsafe is not None, 'negative control did not exercise the missing condition'
    return dict(scope='one separated dodecahedral site pair; all deletion colourings',
                vertices=n, deletions=[sorted(A), sorted(B)],
                colorings=[len(lc), len(rc)], totals=dict(totals),
                omitted_boundary_counterexample=unsafe)


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
