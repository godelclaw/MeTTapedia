#!/usr/bin/env python3
"""Preregistered control for joint-support replacement.

Two three-port cubic vertices glued in port order form the planar theta
multigraph. Each side has exactly the six proper nonzero Tait words.
Prediction: equality of the joint (cut word, observed colour) support
preserves acceptance of every fixed prescription on both sides. Forgetting
the observed colour or misidentifying its dart must fail. This is a tiny
generic Count/gluing control, not a configuration reducibility census.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json


def audit():
    words = list(itertools.permutations(range(1, 4)))
    assert len(words) == 6
    support = set(words)
    joint = [{(w, w[p]) for w in words} for p in range(3)]
    assert all({w for w, _ in j} == support for j in joint)
    checked = rejected = 0
    witness = None
    # Include zero prescriptions: no Tait colouring may realize them.
    for p, q, left, right in itertools.product(range(3), range(3), range(4), range(4)):
        old = any(w[0] == left and (w, right) in joint[p] for w in words)
        new = any(w[0] == left and (w, right) in joint[q] for w in words)
        direct_old = any(w[0] == left and w[p] == right for w in words)
        direct_new = any(w[0] == left and w[q] == right for w in words)
        assert old == direct_old and new == direct_new, "gluing_failure"
        if joint[p] == joint[q]:
            assert old == new, "joint_transport_failure"
            checked += 1
        elif old != new:
            rejected += 1
            if witness is None:
                witness = dict(old_observed_port=p, changed_observed_port=q,
                               exterior_port0_colour=left, prescribed_colour=right,
                               old_accepts=old, changed_accepts=new)
    assert checked == 48 and rejected and witness, "insufficient_controls"
    return dict(status="passed", proper_words=6, all_prescriptions=144,
                joint_equal_controls=checked, marginal_only_failures=rejected,
                specimen=witness,
                scope="theta tangle semantics; no nested-chain or target-class claim")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit()
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(result, indent=2))
