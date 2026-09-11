#!/usr/bin/env python3
"""Preregistered coordinate-factorization gate for physical vertex codes.

Exhaust raw codes at arities at most three, including malformed codes.
The incidence partition must be equivalent to the existing validator;
its input, output and cyclic-star coordinates must be bijective. Compare
the factored colour relation with the independently implemented step.
No planarity, global width bound, or colouring positivity is presumed.
"""

from itertools import product
from v24_vertex_transfer_gate import valid, step


def partition_valid(letter):
    l, r, star, wires = letter
    return (len(set(star)) == 3
            and all((wires[j] is None) == (l + j in star) for j in range(r))
            and all((i in star) == all(w != i for w in wires) for i in range(l))
            and all(j == k or w != v for j, w in enumerate(wires)
                    for k, v in enumerate(wires) if w is not None and v is not None))


def factor(letter):
    l, r, star, wires = letter
    assert partition_valid(letter)
    retained = tuple(j for j in range(r) if wires[j] is not None)
    consumed = tuple(i for i in range(l) if i in star)
    fresh = tuple(j for j in range(r) if wires[j] is None)
    inputs = tuple(wires[j] for j in retained) + consumed
    outputs = retained + fresh
    cyclic = tuple(('in', consumed.index(p)) if p < l
                   else ('out', fresh.index(p - l)) for p in star)
    assert sorted(inputs) == list(range(l))
    assert sorted(outputs) == list(range(r))
    assert set(cyclic) == ({('in', i) for i in range(len(consumed))}
                           | {('out', j) for j in range(len(fresh))})
    assert len(cyclic) == len(set(cyclic)) == 3
    return retained, consumed, fresh, cyclic


def run(bound=3):
    raw = good = colour_pairs = 0
    for l, r in product(range(bound + 1), repeat=2):
        for star in product(range(l + r), repeat=3):
            for wires in product((None,) + tuple(range(l)), repeat=r):
                raw += 1
                letter = l, r, star, wires
                assert partition_valid(letter) == valid(letter), letter
                if not valid(letter):
                    continue
                good += 1
                retained, consumed, fresh, cyclic = factor(letter)
                for x in product(range(3), repeat=l):
                    expected = set(step(letter, x))
                    for y in product(range(3), repeat=r):
                        colour_pairs += 1
                        star_colours = tuple(x[consumed[t]] if side == 'in'
                                             else y[fresh[t]] for side, t in cyclic)
                        actual = (all(y[j] == x[wires[j]] for j in retained)
                                  and len(set(star_colours)) == 3)
                        assert actual == (y in expected), (letter, x, y)
    return dict(bound=bound, raw_codes=raw, valid_codes=good,
                colour_pairs=colour_pairs)


if __name__ == '__main__':
    print(run())
