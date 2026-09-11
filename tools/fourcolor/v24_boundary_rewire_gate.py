#!/usr/bin/env python3
"""Exact permutation gate for first-return surgery at a marked interface.

Preregistered target: if q = p * lift(s), with s permuting just the marked
points, the unmarked cycles are unchanged and R(q) = R(p) * s. Hence the
change in total cycle count is exactly the change in boundary cycle count.
Test every permutation, marked set and marked permutation on up to five
points, including empty interfaces and cycles not touching the interface.
This is permutation surgery, not a four-colouring or catalogue search.
"""

from itertools import combinations, permutations
import json


def cycles(p):
    assert sorted(p) == list(range(len(p)))
    todo, result = set(range(len(p))), set()
    while todo:
        root = min(todo)
        cycle, d = set(), root
        while d not in cycle:
            assert d in todo
            todo.remove(d)
            cycle.add(d)
            d = p[d]
        assert d == root
        result.add(frozenset(cycle))
    return result


def first_return(p, marks):
    assert sorted(p) == list(range(len(p)))
    assert len(set(marks)) == len(marks) and all(0 <= d < len(p) for d in marks)
    result = []
    for x in marks:
        y = p[x]
        while y not in marks:
            y = p[y]
        result.append(marks.index(y))
    return tuple(result)


def run():
    rows = []
    for n in range(6):
        total, changed = 0, 0
        for p in permutations(range(n)):
            cp = cycles(p)
            for k in range(n + 1):
                for marks in combinations(range(n), k):
                    rp = first_return(p, marks)
                    untouched = {c for c in cp if c.isdisjoint(marks)}
                    for s in permutations(range(k)):
                        lift = list(range(n))
                        for i, d in enumerate(marks):
                            lift[d] = marks[s[i]]
                        q = tuple(p[lift[d]] for d in range(n))
                        cq, rq = cycles(q), first_return(q, marks)
                        assert rq == tuple(rp[s[i]] for i in range(k))
                        assert untouched == {c for c in cq if c.isdisjoint(marks)}
                        assert len(cq) + len(cycles(rp)) == len(cp) + len(cycles(rq))
                        total += 1
                        changed += len(cp) != len(cq)
        rows.append(dict(points=n, cases=total, changed_cycle_count=changed))
    return dict(schema='fourcolor-boundary-rewire-v1', rows=rows,
                scope='Exhaustive finite permutation control; generic proof is separate.')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
