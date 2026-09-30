#!/usr/bin/env python3
"""Independently check the finite geometry used by the joint-diamond reduction.

Read the literal source and replacement tables, classify every binary seam
cut, and check the two old-shore extensions of the coupled port block.
This is finite geometric evidence. The arbitrary-exterior reduction and its
normal-form hypotheses are proved separately in Lean.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path

from joint_diamond_occurrence_probe import wiring_tables
from mixed_diamond_reduction_probe import CLASSICAL, ROOT, cycles, read_piece

HERE = Path(__file__).resolve().parent

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "joint-diamond-class-probe.json")
    args = parser.parse_args()
    piece = read_piece("JointDiamondTangle.lean", 14, 34, 8)
    rotation, seam = wiring_tables()
    blocks = [{0, 1}, {4, 5}, {2, 3, 6, 7}]
    masks = [tuple(int(j in block) for j in range(8)) for block in blocks]
    constant = {(0,) * 8, (1,) * 8}
    allowed = constant | set(masks) | {tuple(1 - a for a in mask) for mask in masks}
    cost_counts, zero = Counter(), []
    for assignment in product((0, 1), repeat=10):
        boundary, core = assignment[:8], assignment[8:]
        bits = boundary + (core[0],) * 3 + (core[1],) * 3
        cost = sum(bits[i] != bits[j] for i, j in enumerate(seam) if i < j)
        cost_counts[cost] += 1
        if cost == 0:
            assert boundary in allowed
            zero.append(assignment)
        if boundary in constant and cost <= 1:
            assert core == (boundary[0],) * 2
    assert len(zero) == 8

    old_edges = [(piece["vertex"][d], piece["vertex"][e])
                 for d, e in enumerate(piece["alpha"]) if d < e]
    old_ports = piece["vertex"][34:]
    assert len(old_edges) == 17
    extensions = []
    for i, shore in [(0, {0, 1}), (1, {8, 9}), (2, {2, 3, 5, 6}),
                     (2, set(range(14)) - {0, 1, 8, 9})]:
        internal_cut = sum((v in shore) != (w in shore) for v, w in old_edges)
        seam_cut = sum(bool(masks[i][j]) != (v in shore) for j, v in enumerate(old_ports))
        cost = internal_cut + seam_cut
        assert cost == (4 if i == 2 else 2)
        extensions.append({"ports": sorted(blocks[i]), "core_shore": sorted(shore),
                           "core_shore_vertices": len(shore), "internal_edges_cut": internal_cut,
                           "seam_edges_cut": seam_cut, "total_edges_cut": cost})

    backward = [(i - 1) % 8 for i in range(8)]
    old_before = backward + [8 + (i + 1) % 8 for i in range(8)]
    old_swap = list(range(8, 16)) + list(range(8))
    old_after = [old_before[old_swap[i]] for i in range(16)]
    new_before = backward + [8 + j for j in rotation]
    new_after = [new_before[seam[i]] for i in range(14)]
    old_shift = piece["open_faces"] + len(cycles(old_after)) - len(cycles(old_before))
    new_shift = len(cycles(rotation)) + len(cycles(new_after)) - len(cycles(new_before))
    assert (old_shift, new_shift) == (11, 5)
    # Old core has 17 internal and eight cut edges; the wiring has seven edges.
    decreases = {"vertices": 14 - 2, "edges": 17 + 8 - 7, "faces": old_shift - new_shift}
    assert decreases == {"vertices": 12, "edges": 18, "faces": 6}
    assert decreases["vertices"] - decreases["edges"] + decreases["faces"] == 0
    sources = [Path(__file__), HERE / "joint_diamond_occurrence_probe.py",
               HERE / "mixed_diamond_reduction_probe.py", CLASSICAL / "JointDiamondTangle.lean",
               CLASSICAL / "DiamondCoupledWiringRotation.lean"]
    report = {
        "scope": "Independent finite checks of literal cut extensions and boundary face counts; not a universal reduction proof or a coverage theorem.",
        "seam_assignments_checked": sum(cost_counts.values()),
        "seam_edge_cut_distribution": dict(sorted(cost_counts.items())),
        "zero_cut_assignments": zero,
        "port_blocks": [sorted(block) for block in blocks],
        "old_core_extensions": extensions,
        "face_boundary_cycles": {"old_before": cycles(old_before), "old_after": cycles(old_after),
                                 "new_before": cycles(new_before), "new_after": cycles(new_after)},
        "face_count_relative_to_open_exterior": {"original": old_shift, "replacement": new_shift},
        "whole_map_decreases": decreases,
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sources}}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"seam_assignments": sum(cost_counts.values()),
                      "zero_cuts": len(zero), "old_core_extensions": len(extensions),
                      "whole_map_decreases": decreases}))


if __name__ == "__main__":
    main()
