# FourColor Proof State

Last updated: 2026-06-28 on `fourcolor/cont-20260626`.

This file tracks the two active route forks.  The Four Color Theorem is not
claimed here; the target is a decided state for the Goertzel theorem-4.9 route.

## Fork State

| Fork | State | PLN STV | ITV | Progress |
|---|---|---:|---:|---:|
| Geometric CAP5/Jordan repair | Multiple repairs are refuted; still missing the single structural obstruction theorem that retires the fork. | `<0.42,0.60>` | `[0.25,0.65]` | 62% |
| Algebraic F2 cancellation oracle | Lab finds no top-level all-interior evader on 65 records and no declared-forced evader on the 36 forcing records; Lean now proves the route-facing classifier-control iff/no-evader contract, the target-dimension fork theorem below-bound classifier implies genuine target evader, the full no-evader + closed-checker synthesis handoff, the all-interior success-or-remaining-edge frontier, the executable empty-worklist certificate, the closed-report failure branch as a genuine F2 evader plus a remaining worklist edge, and the target-control bridge reducing any remaining closed-checker failure to an off-target boundary-zero evader. Uniform exclusion of that off-target evader from exact shell data is not yet proved. | `<0.42,0.69>` | `[0.29,0.60]` | 66% |

## Latest Move-2 Evidence

- Lab command archived locally as
  `fourcolor-move2-f2-oracle-validation-lab-20260628.log`.
- JSON snapshot archived locally as
  `fourcolor-move2-f2-oracle-validation-lab-20260628.json`.
- Result summary: 65 records; no top-level all-interior, declared-forced, or
  all-forcing F2 evader flags; crux report keeps the algebraic-F2 implication
  alive and rejects the outside-crossing geometric crux on generated two-band
  annuli.
- Lean theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.forcedEdgeBoundaryTargetCoverage_iff_no_targetEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_no_evader_of_no_missing_finsetControl`.
- Follow-up lab rerun archived locally as
  `fourcolor-move2-interior-frontier-validation-lab-20260628.log`.
- New Lean frontier:
  `CAP5TransportedEdgeComponentCoverCore.interiorSupportForced_synthesis_and_boundaryTargetCoverage`
  and
  `CAP5TransportedEdgeComponentCoverCore.interiorSupportForced_or_remainingEdge`.
  If the closed primitive checker enumerates every ambient interior-support
  edge as forced, synthesis and target coverage follow; otherwise the
  canonical worklist exposes a concrete remaining interior-support edge.
- Empty-worklist lab rerun archived locally as
  `fourcolor-move2-empty-worklist-validation-lab-20260628.log`.
- Executable certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_synthesis_and_targetCoverage`
  and
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_report_synthesis_and_targetCoverage`.
  An empty canonical interior-support worklist plus the closed primitive
  checker report now directly yields synthesis and target coverage.
- Closed-report failure-frontier focused build archived locally as
  `fourcolor-move2-evader-frontier-focused-build-20260628.log`.
- New Lean frontier:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`.
  With an empty executable checker report, failed synthesis now carries both a
  genuine selected-boundary-zero evader for the enumerated forced edges and a
  concrete remaining interior-support edge whose erasure decreases the finite
  worklist.
- Classifier no-evader lab rerun archived locally as
  `fourcolor-move2-classifier-noevader-lab-20260628.json`; exported 65
  projected-generator certificate files and 80 rejected counterexample files.
  In the record signatures, `f2_all_interior_boundary_zero_only_no_evader` and
  `f2_all_interior_boundary_zero_plus_kirchhoff_no_evader` are true on all 65
  records, while the declared-forced variants are true on the 36 records with
  nonempty forcing interior edges.  The algebraic-F2 cruxes
  `forcing_edges_to_f2_all_interior_boundary_zero_control` and
  `forcing_edges_to_f2_all_interior_boundary_zero_kirchhoff_control` still
  survive with support 36 and purified support 18.
- Route-facing classifier theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryTargetClassifierControl_iff_no_targetEvader`.
  These prove that the emitted classifier coordinates control the theorem-4.9
  boundary target exactly when no nonzero target chain evades every enumerated
  CAP5 forced edge.
- Target-dimension fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_theorem49BoundaryTargetEvader_of_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_lt`
  and
  `CAP5TransportedEdgeComponentCoverCore.edge_card_le_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_of_no_targetEvader`.
  These prove that an underdimensioned classifier produces a genuine nonzero
  `W0(H)` evader, while any no-evader CAP5 classifier must meet the
  boundary-zero plus theorem-4.9 Kirchhoff target dimension lower bound.
- Off-target bridge theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_offTargetBoundaryZeroEvader_of_no_missing_finsetControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.offTargetBoundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`.
  These prove that target classifier control closes the completed checker once
  off-target boundary-zero evaders are excluded, and conversely any failed
  closed checker under target control exposes exactly such an off-target
  evader plus the decreasing interior-support worklist edge.

## Remaining Completion Requirements

- Move 1: prove a single fundamental obstruction for the repaired
  CAP5/Jordan geometric class, not another isolated repair-packet failure.
- Move 2: either prove that exact shell/CAP5 data excludes the off-target
  boundary-zero evader left after target classifier control, or exhibit and
  formalize a genuine evader.
- Before any public checkpoint: strict proof-marker scan, trusted-constant audit for new
  theorems, validation lab rerun, full `lake -f lakefile.lean build
  Mettapedia`, and push only to `origin/fourcolor/cont-20260626`.
