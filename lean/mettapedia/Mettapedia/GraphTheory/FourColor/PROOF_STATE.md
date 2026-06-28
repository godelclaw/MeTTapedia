# FourColor Proof State

Last updated: 2026-06-28 on `fourcolor/cont-20260626`.

This file tracks the two active route forks.  The Four Color Theorem is not
claimed here; the target is a decided state for the Goertzel theorem-4.9 route.

## Fork State

| Fork | State | PLN STV | ITV | Progress |
|---|---|---:|---:|---:|
| Geometric CAP5/Jordan repair | The old packet-refutation lane has been consolidated for the source-bound canonical/one-collar part: every closed-walk exact shell structurally blocks the canonical witness choice and every one-collar collar/previous-boundary witness repair by the same two-interior-edge face obstruction. The side-cut lane now has a route-facing obstruction too: any finite support containing an odd closed walk cannot be realized by a single vertex-side cyclic separator, and the CAP5 exceptional outside-crossing normal form inherits that obstruction. Still missing the repair-removal theorem and the proof that the residual side-cut surface must expose such an odd-walk support or reduce to the one-collar face contradiction. | `<0.51,0.66>` | `[0.33,0.68]` | 72% |
| Algebraic F2 cancellation oracle | Lab finds no top-level all-interior evader on 65 records, no declared-forced evader on the 36 forcing records, and no all-interior vertex-Kirchhoff failure on all 65 records; the vertex-failure crux survives on the 36 forcing records. Lean now proves the route-facing classifier-control iff/no-evader contract, the target-dimension fork theorem below-bound classifier implies genuine target evader, the full no-evader + closed-checker synthesis handoff, the all-interior success-or-remaining-edge frontier, the executable empty-worklist certificate, the closed-report failure branch as a genuine F2 evader plus a remaining worklist edge, the target-control bridge reducing any remaining closed-checker failure to an off-target boundary-zero evader, the vertex-Kirchhoff failure bridge making that evader concrete at a theorem-4.9 boundary vertex, the row-span/subset certificate bridge for excluding or exposing that failure, and the exact binary fork theorem. The empty canonical interior-support worklist proves the exact row-span/subset certificate itself and rules out the concrete vertex-Kirchhoff evader branch. New: an odd closed walk entirely inside the ambient interior support forces a nonempty remaining interior-support worklist, with a concrete edge whose erasure decreases the finite worklist. Thus the empty-worklist proof path is not uniform over odd-interior-walk supports; the remaining burden is to prove exact CAP5 data excludes that obstruction while reaching the subset side, or formalize the genuine vertex-Kirchhoff evader produced by failure. | `<0.49,0.74>` | `[0.35,0.64]` | 74% |

## Latest Move-1 Evidence

- Focused geometric build archived locally as
  `fourcolor-move1-one-collar-obstruction-focused-build-20260628.log`.
- Dependency replay repair build archived locally as
  `fourcolor-move1-one-collar-obstruction-dependency-build-20260628.log`.
- New Lean theorem surface:
  `not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell`,
  `not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell`, and
  `not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell`.
  These package the shared geometric obstruction: a closed-walk exact shell
  already forces a face with two distinct interior-support edges, while the
  canonical one-collar witness/collar surfaces can carry at most one such edge
  on that face.  This retires the source-bound canonical and one-collar
  positive-collar repair packet family as one structural theorem family,
  rather than as isolated benchmark failures.
- Side-cut focused build archived locally as
  `fourcolor-move1-odd-sidecut-frontier-focused-build-20260628.log`.
- Validation lab JSON archived locally as
  `fourcolor-move1-odd-sidecut-lab-20260628.json`; the rerun contains 65
  benchmark signatures, 65 projected-generator certificate reports, and 80
  rejected counterexample exports, with empty stderr.
- Axiom audit archived locally as
  `fourcolor-move1-odd-sidecut-axiom-audit-20260628.log`; the new theorem
  constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move1-odd-sidecut-full-build-20260628.log` with 5900 jobs.
- New side-cut theorem surface:
  `not_exists_sideCut_crosses_closed_odd_walk_subset`,
  `not_exists_exceptionalAnnulusCrossingOutsideEdge_of_closed_odd_walk_subset`,
  `closedWalkExactShell_oneCollar_and_oddSideCut_obstruction`, and
  `closedWalkExactShell_oneCollar_and_CAP5OddSideCut_obstruction`.
  These package the two-band triangle failure as a general odd-closed-walk
  cyclic-separator obstruction: no single side predicate can make every edge
  in a finite support cross if that support contains an odd closed walk, and
  the CAP5 outside-crossing normal form cannot repair that.
- Remaining Move-1 burden: prove the residual side-cut/cyclic-separator
  surface always contains such an odd-walk support or reduces to the
  two-interior-edge face contradiction, and push the resulting obstruction
  through repair-removal.

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
- Vertex-Kirchhoff failure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget`,
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl`,
  and
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`.
  These refine the off-target branch to a concrete failed Kirchhoff equation at
  a theorem-4.9 boundary vertex: under target classifier control, a failed
  closed checker exposes a forced-edge-vanishing boundary-zero chain with
  nonzero `vertexKirchhoffSum` at that vertex and the decreasing worklist edge.
- Vertex-failure lab rerun archived locally as
  `fourcolor-move2-subset-certificate-lab-20260628.json`; exported 65
  projected-generator certificate files and 80 rejected counterexample files.
  The new
  `f2_all_interior_boundary_zero_kirchhoff_failure_absent` signature is true
  on all 65 records; the crux packet
  `forcing_edges_to_f2_all_interior_boundary_zero_kirchhoff_failure_absent`
  survives with support 36 and purified support 18.  The focus rows still
  expose smaller-control failure witnesses, e.g. single-spoke/single-shared
  controls produce a nonzero theorem-4.9 boundary-vertex Kirchhoff image.
- Row-span/subset certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`,
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl`.
  These make the remaining exact-shell proof obligation a row-span/subset
  certificate: every boundary-zero chain vanishing on the enumerated forced
  edges must lie in the theorem-4.9 boundary target; failure of that certificate
  is already a genuine vertex-Kirchhoff evader.
- Exact F2 fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl_of_no_missing_finsetControl`.
  These package the surviving algebraic oracle as a binary machine-checked
  decision: the subset certificate closes the target-controlled checker, and
  failure of that certificate is already the concrete evader branch.
- Empty-worklist subset-certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty`,
  `CAP5TransportedEdgeComponentCoverCore.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_interiorEdgeSupport_subset_enumeratedForcedEdges`,
  `CAP5TransportedEdgeComponentCoverCore.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty`,
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_remainingInteriorSupportEmpty`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_remainingInteriorSupportEmpty_of_no_missing_finsetControl`.
  These prove the exact subset certificate on the executable empty-worklist
  shell and collapse the binary F2 fork to synthesis plus target coverage under
  target classifier control and a closed checker.
- Odd-worklist focused build archived locally as
  `fourcolor-move2-odd-worklist-focused-build-20260628.log`.
- Odd-interior worklist theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport`
  and
  `CAP5TransportedEdgeComponentCoverCore.not_remainingInteriorSupportEmpty_of_closed_walk_odd_length_in_interiorSupport`.
  These prove that an odd closed walk supported by ambient interior-support
  edges refutes the executable empty-worklist branch for any Boolean CAP5
  forced-edge classifier: some interior-support edge remains unemitted, and
  erasing it strictly decreases the canonical worklist.

## Remaining Completion Requirements

- Move 1: prove a single fundamental obstruction for the repaired
  CAP5/Jordan geometric class, extending the closed-walk exact-shell
  one-collar obstruction and the odd-walk side-cut obstruction across the
  remaining repair-removal surface.
- Move 2: extend the empty-worklist exact subset certificate to the uniform
  CAP5 shell while excluding the odd-interior-worklist obstruction, or exhibit
  and formalize the genuine vertex-Kirchhoff evader produced by failure of
  that certificate.
- Before any public checkpoint: strict proof-marker scan, trusted-constant audit for new
  theorems, validation lab rerun, full `lake -f lakefile.lean build
  Mettapedia`, and push only to `origin/fourcolor/cont-20260626`.
