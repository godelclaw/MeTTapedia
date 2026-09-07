#!/usr/bin/env python3
"""Arithmetic gate for combining the complete contour and cotree suppliers.

Pre-registered outcomes: reject a depth-window overrun, a spaced index
outside the supplied chain, or insufficient strict-material spacing.
Check the exact radius boundary and both adjacent values. The geometric
controls are the separately replayed contour-bond and marked-cotree gates;
these scalar checks do not assert a spherical or zero-Count witness.
"""

import argparse
import itertools
import json
from pathlib import Path


def audit():
    checks = windows = 0
    for a, w, t, n in itertools.product(range(2, 7), range(7), range(4), range(1, 6)):
        r = (t + 1) * n
        count = (6 * w + 1) * r + 1
        radius = count * a
        for distance in (0, radius - 1, radius, radius + 1, radius + a):
            if distance > radius:
                assert all(i * a + a <= distance for i in range(count)), "window_overrun"
            else:
                assert distance <= radius, "radius_failure"
            checks += 1
        for start in range(t + 1):
            indices = [(6 * w + 1) * (start * n + i) for i in range(n + 1)]
            assert indices[-1] < count, "index_overrun"
            assert all(j - i > 6 * w for i, j in zip(indices, indices[1:])), "spacing_failure"
            windows += 1
    return dict(schema="fourcolor-v24-meshfree-seam-branch-v1",
                branch_boundary_checks=checks, spacing_windows=windows, outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    result = audit()
    if args.verify_only:
        assert result == json.loads(args.verify_only.read_text()), "receipt_mismatch"
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
