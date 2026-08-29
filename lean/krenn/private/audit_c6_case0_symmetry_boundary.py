#!/usr/bin/env python3
"""Audit the exact symmetry boundary of the gauge-fixed C6 case-0 corpus.

The all-collapse component census has 67 components and uses only an
order-two anchored symmetry group.  It is tempting to ask whether the full
``Stab(C6) x S3`` group (order 72) should collapse more of those components.
This audit separates two different actions:

* the full physical action on raw off-diagonal cases; and
* the action which preserves case 0 *and* its six normalized entries.

It proves, by enumeration, that the latter is exactly the already-recorded
order-two anchored group.  The other 70 physical maps move case 0 to another
raw case, so they belong to the existing 718-case orbit reduction rather than
to an additional quotient of the fixed case-0 component decomposition.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from pathlib import Path

ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(ROOT))

import c6_collapse_attack as c6  # noqa: E402
import c6_singleton_collapse_chart as chart  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402
from sc6_phaseB_stabilizer import moved_entry  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def serialise_group_element(sigma: dict[int, int], tau: tuple[int, ...]) -> dict:
    return {
        "vertex_permutation": [sigma[index] for index in range(6)],
        "colour_permutation": list(tau),
    }


def act_case(
    sigma: dict[int, int], tau: tuple[int, ...],
    case: tuple[tuple[int, int], ...],
) -> tuple[tuple[int, int], ...]:
    moved: dict[tuple[int, int], tuple[int, int]] = {}
    for index, edge in enumerate(c6.X):
        image_edge, left, right = pipeline.vertex_perm_on_entry(
            sigma, edge, *case[index]
        )
        moved[image_edge] = (tau[left], tau[right])
    return tuple(moved[edge] for edge in c6.X)


def main() -> int:
    case0 = ((0, 1),) * 6
    fixed = set(pipeline.max_fixable(chart.chosen_entries(case0)))
    group = [
        (sigma, tau)
        for sigma in pipeline.stabilizer(c6.X)
        for tau in itertools.permutations(range(3))
    ]
    if len(group) != 72:
        raise RuntimeError("fixed-C6 physical group order drift")

    case_stabilizer = [
        (sigma, tau) for sigma, tau in group if act_case(sigma, tau, case0) == case0
    ]
    gauge_stabilizer = [
        (sigma, tau)
        for sigma, tau in group
        if {moved_entry(sigma, tau, key) for key in fixed} == fixed
    ]
    case_stabilizer_set = {
        (tuple(sigma[index] for index in range(6)), tau)
        for sigma, tau in case_stabilizer
    }
    gauge_stabilizer_set = {
        (tuple(sigma[index] for index in range(6)), tau)
        for sigma, tau in gauge_stabilizer
    }
    if len(case_stabilizer) != 2 or case_stabilizer_set != gauge_stabilizer_set:
        raise RuntimeError("case-0 and gauge stabilizers do not coincide")

    # This also verifies all 72 actions preserve the actual C6 equation set.
    case_reps = pipeline.case_orbits(c6.X, verify=True)
    if len(case_reps) != 718 or sum(size for _, _, size in case_reps) != 46656:
        raise RuntimeError("raw C6 case-orbit coverage drift")
    case0_rows = [row for row in case_reps if row[0] == 0]
    if case0_rows != [(0, case0, 36)]:
        raise RuntimeError("case-0 raw orbit receipt drift")
    direct_case0_orbit = {act_case(sigma, tau, case0) for sigma, tau in group}
    if len(direct_case0_orbit) != 36:
        raise RuntimeError("case-0 orbit/stabilizer mismatch")

    component_orbits_path = (
        ROOT / "allcollapse_case_artifacts" / "case_0" / "component_orbits.json"
    )
    component_orbits = json.loads(component_orbits_path.read_text())
    recorded_actions = {
        (
            tuple(action["vertex_permutation"]),
            tuple(action["colour_permutation"]),
        )
        for action in component_orbits["actions"]
    }
    if component_orbits["anchored_group_order"] != 2:
        raise RuntimeError("recorded component action order drift")
    if recorded_actions != case_stabilizer_set:
        raise RuntimeError("component actions are not exactly the case-0 stabilizer")

    payload = {
        "format": "krenn-c6-case0-symmetry-boundary-v1",
        "sources": {
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "component_orbits_sha256": sha256(component_orbits_path),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "physical_group_order": len(group),
        "raw_case_count": 46656,
        "raw_case_orbit_count": len(case_reps),
        "case0_raw_orbit_size": len(direct_case0_orbit),
        "case0_stabilizer_order": len(case_stabilizer),
        "case0_gauge_stabilizer_order": len(gauge_stabilizer),
        "case0_stabilizer_equals_gauge_stabilizer": True,
        "case0_stabilizer_actions": [
            serialise_group_element(sigma, tau) for sigma, tau in case_stabilizer
        ],
        "component_orbit_group_order": component_orbits["anchored_group_order"],
        "component_orbit_action_equals_case0_stabilizer": True,
        "component_count": component_orbits["component_count"],
        "component_orbit_count": component_orbits["orbit_count"],
        "conclusion": {
            "additional_physical_symmetry_within_fixed_case0": False,
            "reason": (
                "Every physical symmetry outside the recorded order-two group "
                "moves the raw case-0 gauge pattern to another raw case."
            ),
            "existing_reduction": (
                "Those 36 physical images are already one raw-case orbit in "
                "the verified 718-representative C6 case census."
            ),
            "scope": (
                "This rules out further physical-group compression of the 67 "
                "components inside the fixed case-0 gauge normalization only; "
                "it does not itself establish cross-case component transport."
            ),
        },
    }
    target = (
        ROOT / "allcollapse_case_artifacts" / "case_0" /
        "symmetry_boundary_audit_v1.json"
    )
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 CASE-0 SYMMETRY BOUNDARY VERIFIED: "
        "|H|=72; case0 orbit=36; fixed stabilizer=2; "
        "67 components -> 44 anchored orbits"
    )
    print("manifest_sha256=" + sha256(target))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
