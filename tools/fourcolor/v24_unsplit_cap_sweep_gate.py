#!/usr/bin/env python3
"""Gate the full interface of a sideways sweep with both caps unsplit.

The controls are a single zigzag ring between two cyclic caps. The shell
alone is a cycle and has a width-two consecutive sweep. Pre-registered
claim to test: at a half-shell cut, every choice of whole-cap ownership
has at least n original crossing edges. This is a geometry/arity test,
not a colouring census or a configuration-reduction catalogue.
"""
import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_geodesic_mincut_gate import connected, validate_sphere


def graph(n):
    assert n >= 3
    v = lambda row,i: row*n+i%n
    edges = []
    for kind in range(6):
        for i in range(n):
            edges.append(sorted([(v(0,i),v(0,i+1)), (v(0,i),v(1,i)),
                          (v(1,i),v(2,i)), (v(2,i),v(1,i+1)),
                          (v(2,i),v(3,i)), (v(3,i),v(3,i+1))][kind]))
    faces = [[v(0,i) for i in range(n)], [v(3,i) for i in range(n)]]
    for i in range(n):
        faces += [[v(0,i),v(0,i+1),v(1,i+1),v(2,i),v(1,i)],
                  [v(3,i),v(3,i+1),v(2,i+1),v(1,i+1),v(2,i)]]
    return dict(primal_vertex_count=4*n, primal_edges=edges, face_cycles=faces)


def cut(edges, side):
    return [i for i,(u,v) in enumerate(edges) if (u in side)!=(v in side)]


def run():
    rows = []
    for n in range(3,9):
        g = graph(n)
        validate_sphere(g)
        edges = g['primal_edges']
        assert len(set(tuple(sorted(e)) for e in edges)) == len(edges)
        assert connected(4*n,edges,set(range(4*n)))
        assert all(connected(4*n,edges[:i]+edges[i+1:],set(range(4*n))) for i in range(len(edges)))
        shell = set(range(n,3*n))
        caps = [set(range(n)),set(range(3*n,4*n))]
        assert connected(4*n,edges,shell)
        assert all(connected(4*n,edges,c) and connected(4*n,edges,set(range(4*n))-c) for c in caps)
        internal = [e for e in edges if set(e) <= shell]
        order = [v for i in range(n) for v in (n+i,2*n+i)]
        assert all(len(cut(internal,set(order[:t]))) == 2 for t in range(1,2*n))
        minimum = len(edges)
        counts = 0
        witness = None
        for xs in itertools.combinations(sorted(shell),n):
            for a,b in itertools.product((False,True),repeat=2):
                side = set(xs) | (caps[0] if a else set()) | (caps[1] if b else set())
                width = len(cut(edges,side))
                assert width >= n
                if width < minimum:
                    minimum, witness = width, dict(shell=xs,outer_inside=a,inner_inside=b)
                counts += 1
        # A permissive control: split the caps along with the shell. This is
        # a whole-graph slice, and its full interface stays bounded here.
        split_width = max(len(cut(edges,{r*n+i for r in range(4) for i in range(t)}))
                          for t in range(1,n))
        assert split_width == 6
        rows.append(dict(circumference=n,vertices=4*n,half_cuts=counts,
                         minimum_full_width=minimum,internal_sweep_width=2,
                         split_cap_slice_width=split_width,witness=witness))
    return dict(schema='fourcolor-v24-unsplit-cap-sweep-v1',receipts=rows,
                scope='whole caps only; not a lower bound when caps may be split, or a zero-Count obstruction')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        atomic_write_json(args.output,result)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':
    main()
