#!/usr/bin/env python3
"""Gate for finite per-shore return records with absent and aliased names.

Preregistered: padded return permutation plus optional name coordinates
determines a correspondence of observed points preserving every name and
every first return. Equal records must be interchangeable under arbitrary
rewiring supported on the observed points. Neither presence nor aliases
may be forgotten. No colouring data is generated.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_marked_face_return_gate import compressed, compose, extend, partition, stretch


def record(p, names):
    points = tuple(dict.fromkeys(x for x in names if x is not None))
    indices = {x: i for i, x in enumerate(points)}
    labels = tuple(None if x is None else indices[x] for x in names)
    ret = compressed(p, points) + tuple(range(len(points), len(names)))
    return (ret, labels), points


def named_partition(p, names):
    blocks = partition(p)
    return tuple(None if x is None or y is None else
                 any(x in b and y in b for b in blocks)
                 for x in names for y in names)


def audit():
    records, cases, replacements = {}, 0, 0
    for n in range(1, 5):
        for p in itertools.permutations(range(n)):
            for names in itertools.product((None,) + tuple(range(n)), repeat=3):
                code, hit = record(p, names)
                cases += 1
                q, other_names, other_hit = records.setdefault(code, (p, names, hit))
                assert len(hit) == len(other_hit)
                for tau in itertools.permutations(range(len(hit))):
                    left = compose(p, extend(tau, hit, len(p)))
                    right = compose(q, extend(tau, other_hit, len(q)))
                    assert named_partition(left, names) == named_partition(right, other_names)
                    replacements += 1
    stretch_cases = 0
    for p in itertools.permutations(range(4)):
        for names in ((0, 0, 1), (0, None, 3), (None, None, None), (3, 1, 2)):
            code, _ = record(p, names)
            for extra in (1, 5, 31):
                q = stretch(p, extra)
                assert record(q, names)[0] == code
                stretch_cases += 1
    p = (0, 1)
    absent_left, _ = record(p, (0, None, 1))
    absent_right, _ = record(p, (0, 1, None))
    assert absent_left[0] == absent_right[0] and absent_left != absent_right
    alias_left, _ = record(p, (0, 1, 0))
    alias_right, _ = record(p, (0, 1, 1))
    assert alias_left[0] == alias_right[0] and alias_left != alias_right
    assert named_partition(p, (0, 1, 0)) != named_partition(p, (0, 1, 1))
    return dict(schema='fourcolor-v24-named-face-record-v1', named_cases=cases,
                distinct_records=len(records), supported_replacement_checks=replacements,
                stretched_carrier_checks=stretch_cases,
                omission_controls=['presence is necessary', 'alias coordinates are necessary'],
                scope='Finite named permutation records, not a supplied Count seam.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    receipt = audit()
    if args.output:
        atomic_write_json(args.output, receipt)
    if args.check:
        assert receipt == json.loads(args.check.read_text())
    print(json.dumps(receipt, indent=2))
