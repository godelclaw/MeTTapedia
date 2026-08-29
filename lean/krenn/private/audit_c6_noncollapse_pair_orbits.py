#!/usr/bin/env python3
"""Audit physical C6 non-collapse branch types above the case-0 gauge orbit.

The strict eleven-row certificate is presently transported across all 36 raw
gauge cases in the physical orbit of case 0, but only for its designated
non-collapse slot.  This audit identifies the correct finite quotient before
we try to derive any further certificate mechanism.

A branch point is a triple ``(raw_case, vertex, colour)``.  The first member
selects the six off-diagonal gauge choices on C6; the latter two select the
theta minor whose non-vanishing gives the two incident P-kills.  The physical
group ``Stab(C6) x S3`` acts on all three pieces.  The audit proves that the
648 branch points over the 36-case physical orbit of case 0 split into twelve
orbits.  Thus a proof mechanism for one representative of each listed type,
transported by checked physical symmetry, covers this designated branch family.

It deliberately does *not* claim that the P-kills follow in every branch, or
that the eleven-row core applies to the other eleven types.  It is a finite
scope reduction and a provenance receipt only.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from pathlib import Path
from typing import Iterable


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402


Case = tuple[tuple[int, int], ...]
Pair = tuple[Case, int, int]
GroupElement = tuple[dict[int, int], tuple[int, ...]]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def serialise_case(case: Case) -> list[list[int]]:
    return [list(entry) for entry in case]


def serialise_action(sigma: dict[int, int], tau: tuple[int, ...]) -> dict:
    return {
        "vertex_permutation": [sigma[index] for index in range(6)],
        "colour_permutation": list(tau),
    }


def act_case(sigma: dict[int, int], tau: tuple[int, ...], case: Case) -> Case:
    moved: dict[tuple[int, int], tuple[int, int]] = {}
    for index, edge in enumerate(c6.X):
        image_edge, left, right = pipeline.vertex_perm_on_entry(
            sigma, edge, *case[index]
        )
        moved[image_edge] = (tau[left], tau[right])
    return tuple(moved[edge] for edge in c6.X)


def act_pair(element: GroupElement, pair: Pair) -> Pair:
    sigma, tau = element
    case, vertex, colour = pair
    return act_case(sigma, tau, case), sigma[vertex], tau[colour]


def orbit(group: Iterable[GroupElement], point: Pair) -> set[Pair]:
    return {act_pair(element, point) for element in group}


def main() -> int:
    case0: Case = ((0, 1),) * len(c6.X)
    group: list[GroupElement] = [
        (sigma, tau)
        for sigma in pipeline.stabilizer(c6.X)
        for tau in itertools.permutations(range(3))
    ]
    if len(group) != 72:
        raise RuntimeError("C6 physical group order drift")

    case_orbit = {act_case(sigma, tau, case0) for sigma, tau in group}
    if len(case_orbit) != 36:
        raise RuntimeError("case-0 raw orbit receipt drift")

    case0_stabilizer = [
        element for element in group if act_case(*element, case0) == case0
    ]
    if len(case0_stabilizer) != 2:
        raise RuntimeError("case-0 stabilizer order drift")

    universe: set[Pair] = {
        (case, vertex, colour)
        for case in case_orbit
        for vertex in range(6)
        for colour in range(3)
    }
    if len(universe) != 648:
        raise RuntimeError("raw pair universe count drift")

    seen: set[Pair] = set()
    records: list[dict] = []
    for point in sorted(universe):
        if point in seen:
            continue
        points = orbit(group, point)
        if not points <= universe:
            raise RuntimeError("physical action escaped case-0 pair universe")
        seen |= points
        case0_points = sorted(
            (vertex, colour)
            for case, vertex, colour in points
            if case == case0
        )
        if not case0_points:
            raise RuntimeError("physical pair orbit missed the case-0 slice")
        representative_vertex, representative_colour = case0_points[0]
        representative: Pair = (case0, representative_vertex, representative_colour)
        stabilizer = [
            element for element in group if act_pair(element, representative) == representative
        ]
        if len(points) * len(stabilizer) != len(group):
            raise RuntimeError("pair orbit/stabilizer mismatch")
        slice_from_stabilizer = sorted({
            (sigma[representative_vertex], tau[representative_colour])
            for sigma, tau in case0_stabilizer
        })
        if slice_from_stabilizer != case0_points:
            raise RuntimeError("case-0 pair slice is not its stabilizer orbit")
        records.append({
            "representative": {
                "case": serialise_case(case0),
                "vertex": representative_vertex,
                "colour": representative_colour,
            },
            "orbit_size": len(points),
            "stabilizer_size": len(stabilizer),
            "case0_slice_slots": [
                {"vertex": vertex, "colour": colour}
                for vertex, colour in case0_points
            ],
            "case0_slice_size": len(case0_points),
        })

    records.sort(key=lambda row: (
        row["representative"]["vertex"], row["representative"]["colour"]
    ))
    if len(seen) != len(universe) or len(records) != 12:
        raise RuntimeError("non-collapse pair-orbit coverage drift")
    if [record["orbit_size"] for record in records].count(36) != 6:
        raise RuntimeError("unexpected size-36 orbit count")
    if [record["orbit_size"] for record in records].count(72) != 6:
        raise RuntimeError("unexpected size-72 orbit count")

    transport_path = (
        ROOT / "noncollapse_case_artifacts" /
        "slot0_profile321_caseorbit_transport_v1" / "manifest.json"
    )
    transport = json.loads(transport_path.read_text())
    transport_pairs = {
        (
            tuple(tuple(entry) for entry in row["target_case"]),
            row["target_slot"]["vertex"],
            row["target_slot"]["colour"],
        )
        for row in transport.get("rows", [])
    }
    seed_orbit = orbit(group, (case0, 0, 0))
    if not transport.get("all_strict"):
        raise RuntimeError("existing eleven-row transport is not all strict")
    if transport_pairs != seed_orbit:
        raise RuntimeError("eleven-row transport does not cover exactly its pair orbit")

    payload = {
        "format": "krenn-c6-noncollapse-pair-orbits-v1",
        "sources": {
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "existing_elevenrow_transport_manifest_sha256": sha256(transport_path),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "physical_group_order": len(group),
        "case0_raw_orbit_size": len(case_orbit),
        "slots_per_raw_case": 18,
        "raw_pair_count": len(universe),
        "pair_orbit_count": len(records),
        "pair_orbits": records,
        "existing_elevenrow_branch": {
            "seed": {"vertex": 0, "colour": 0},
            "pair_orbit_index": next(
                index for index, record in enumerate(records)
                if record["representative"]["vertex"] == 0
                and record["representative"]["colour"] == 0
            ),
            "transported_strict_leaf_count": len(transport_pairs),
            "transport_covers_exactly_its_physical_pair_orbit": True,
        },
        "conclusion": {
            "finite_reduction": (
                "The 648 designated non-collapse branch points over the raw "
                "case-0 orbit reduce to 12 physical branch types."
            ),
            "not_established": (
                "Neither the two P-kills nor a certificate core is proved for "
                "the other eleven types by this audit."
            ),
        },
    }
    target = ROOT / "noncollapse_case_artifacts" / "noncollapse_pair_orbit_audit_v1.json"
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 NON-COLLAPSE PAIR ORBITS VERIFIED: "
        "648 raw pairs -> 12 physical types; "
        "eleven-row transport = exactly type (v=0,c=0)"
    )
    print("manifest_sha256=" + sha256(target))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
