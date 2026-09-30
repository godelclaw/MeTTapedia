#!/usr/bin/env python3
"""Independently replay the cyclic-interval obstruction and actual face patterns.

The Python checks are evidence alongside the Lean boundary-clearance theorem.
They do not certify internal-six connectivity of the fixture maps.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from mixed_diamond_reduction_probe import HERE, ROOT, CLASSICAL, cycles, read_piece

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "alternating-lobe-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "joint-diamond-clearance-probe.json")
    args = parser.parse_args()
    piece = read_piece("JointDiamondTangle.lean", 14, 34, 8)
    source = CLASSICAL / "JointDiamondChord.lean"
    match = re.search(r'def nextPortCodes : String := "([A-I]+)"', source.read_text())
    assert match
    tags = [ord(c) - ord("A") for c in match.group(1)]
    assert len(tags) == 42
    capped = piece["alpha"] + list(range(34, 42))
    phi = [piece["rho"][capped[d]] for d in range(42)]
    for orbit in cycles(phi):
        for d in orbit:
            if not any(x >= 34 for x in orbit):
                assert tags[d] == 8
                continue
            x = d
            while x < 34:
                x = phi[x]
            assert tags[d] == x - 34

    def label(p, q, d):
        offset = (tags[d] + 8 - p) % 8
        return tags[d] < 8 and 0 < offset <= (q + 8 - p) % 8

    transitions, separated = 0, []
    for p in range(8):
        for q in range(8):
            alpha = capped.copy()
            alpha[34 + p], alpha[34 + q] = 34 + q, 34 + p
            changed = [piece["rho"][alpha[d]] for d in range(42)]
            for d in range(42):
                assert label(p, q, changed[d]) == label(p, q, d)
                transitions += 1
            b, c = (p + 1) % 8, (q + 1) % 8
            if p != q and b != q and c != p:
                assert label(p, q, 34 + b) != label(p, q, 34 + c)
                assert not any(34 + b in orbit and 34 + c in orbit for orbit in cycles(changed))
                separated.append([p, q, b, c])
    assert transitions == 2688 and len(separated) == 40
    subprocess.run([sys.executable, str(HERE / "joint_diamond_face_probe.py"),
                    "--fixtures", str(args.fixtures), "--output", str(args.output)], check=True)
    report = json.loads(args.output.read_text())
    report["status"] = "independent replay accompanying kernel-checked complete four-face recognition"
    report["kernel_consumer"] = "FourColor.JointDiamondPatch.Tangle.FaceClearance.boundary_clear"
    report["remaining_theorem"] = "Geometric supply or broader family coverage for the full target graph class."
    report["chord_test_scope"] = (
        "All 64 port pairs preserve the cyclic-interval label on 42 darts. Forty ordered "
        "nonadjacent pairs separate surviving boundary ports. Girth leaves twelve unordered "
        "chords. The Lean consumer independently derives genuine remaining ports, connected "
        "shores and the exact capped-face conjugacy in an arbitrary qualifying map.")
    report["interval_check"] = {"label_characters": 42, "port_pairs": 64,
                                "dart_transitions": transitions,
                                "separated_ordered_pairs": separated}
    for path in [Path(__file__), source,
                 CLASSICAL / "JointDiamondFaceClearance.lean",
                 CLASSICAL / "JointDiamondClearanceAudit.lean",
                 ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/PartialCubicDartBoundaryCompletion.lean"]:
        report["source_sha256"][str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"stats": report["stats"], "interval_transitions": transitions,
                      "separated_ordered_chords": len(separated)}, sort_keys=True))


if __name__ == "__main__":
    main()
