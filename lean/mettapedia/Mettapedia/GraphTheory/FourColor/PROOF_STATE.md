# FourColor Proof State

Last updated: 2026-06-29 on `fourcolor/cont-20260626`.

This file tracks the two active route forks.  The Four Color Theorem is not
claimed here; the target is a decided state for the Goertzel theorem-4.9 route.

## Fork State

| Fork | State | PLN STV | ITV | Progress |
|---|---|---:|---:|---:|
| Geometric CAP5/Jordan repair | The old packet-refutation lane has been consolidated for the source-bound canonical/one-collar part: every closed-walk exact shell structurally blocks the canonical witness choice and every one-collar collar/previous-boundary witness repair by the same two-interior-edge face obstruction. The side-cut lane has two structural obstructions now: any finite support containing an odd closed walk cannot be realized by a single vertex-side cyclic separator, and any CAP5/Jordan exceptional candidate realized as cyclic-cut data produces a forbidden cyclic edge cut of size at most four in a cyclically five-edge-connected graph. The generated residual surface is now classified too: under cyclic five-edge-connectivity every generated node is either missing primitive checker evidence or emits a concrete outside-crossing edge outside candidate support; at report level, all 16 latents are forced exactly when the missing-evidence frontier is empty, and failure returns a concrete missing-evidence latent. Still missing the theorem that exact CAP5/Jordan shell data eliminates that primitive missing-evidence branch or reduces it to the odd-walk obstruction, the realized small-cut obstruction, or the one-collar face contradiction. | `<0.60,0.72>` | `[0.43,0.71]` | 82% |
| Algebraic F2 cancellation oracle | Lab finds no top-level all-interior evader on 65 records, no declared-forced evader on the 36 forcing records, and no all-interior vertex-Kirchhoff failure on all 65 records; the vertex-failure crux survives on the 36 forcing records. Lean now proves the route-facing classifier-control iff/no-evader contract, including the full selected-boundary-zero version: emitted CAP5 coordinates control every selected-boundary-zero chain iff no nonzero selected-boundary-zero chain evades all enumerated forced edges. The completed-checker no-evader handoff now also returns full boundary-zero classifier control together with theorem-4.9 synthesis. The executable report bridge now consumes the generator verdict `forcedCounterexampleLatents = all`: under cyclic five-edge-connectivity that verdict closes the primitive missing-evidence frontier, so the report-forced-all branch feeds directly into full boundary-zero no-evader control, the empty-worklist subset certificate, and the target-controlled synthesis-or-genuine-evader fork. The empty-worklist subset certificate is now the actual no-evader branch too: if the forced-all report has no remaining canonical interior-support worklist, Lean proves there is no nonzero selected-boundary-zero evader and then closes synthesis plus full selected-boundary-zero classifier control. The forced-all finite scheduler fork packages the remaining exact-shell obligation: either that empty-worklist no-evader/full-control branch holds, or there is a concrete remaining interior-support edge whose erasure strictly decreases the finite worklist. The forced-all residual scheduler fork now strengthens the failure side: if synthesis fails under the forced-all report, Lean returns the complete checker histogram, forced-bin detector payload, a genuine selected-boundary-zero evader, a traced remaining interior-support edge in the residual worklist, and a strict residual decrease after recording that edge as processed. The residual scheduler transition now also proves that the chosen edge is not controlled by the immutable classifier output and returns the exact one-edge emitted/control update needed to insert it into the processed scheduler state. The terminal residual scheduler theorem closes the success side: if the explicit residual interior-support worklist is exhausted while the processed-control invariant holds, Lean proves no selected-boundary-zero evader exists and closes theorem-4.9 synthesis plus full selected-boundary-zero classifier control. The failed-terminal scheduler decision now connects the two sides: under forced-all and processed-control, failed synthesis cannot have an exhausted residual worklist, and Lean returns a genuine selected-boundary-zero evader plus the next residual edge, immutable-control failure for that edge, the one-edge emitted/control update, and strict residual decrease. The immutable-scheduler obstruction now proves that the same returned edge cannot be silently inserted into the processed state under the original classifier output: processing it is invalid unless the scheduler promotes new emitted/control information, or the returned boundary-zero chain is accepted as the obstruction. The route-facing residual scheduler decision now packages the live finite state as terminal no-evader/synthesis, already-closed synthesis, or a promoted one-edge obstruction with immutable processing ruled out and strict residual decrease. The forced-all F2 oracle is also packaged as a direct route-facing split: either no-evader closes synthesis plus full selected-boundary-zero classifier control, or Lean returns an actual nonzero selected-boundary-zero evader. The same report-forced-all interface is now split into its two decision halves: target control plus absence of the concrete theorem-4.9 boundary-vertex Kirchhoff evader yields synthesis and target coverage, while target control plus failed synthesis returns that genuine evader and a decreasing remaining-worklist edge. The forced-all branch now also exposes the pure F2 failure fork without target control: failed synthesis itself returns a nonzero selected-boundary-zero chain vanishing on every enumerated forced edge plus a decreasing remaining interior-support worklist edge. Its stronger canonical path-xor payload form returns the detector payload, a selected-boundary-zero chain, a concrete non-forced remaining interior edge where the chain is nonzero, a strict worklist decrease, and a nonzero canonical red/blue family pairing. Lean also proves the target-dimension fork theorem below-bound classifier implies genuine target evader, the target-control/off-target bridge, the vertex-Kirchhoff failure bridge, the row-span/subset certificate bridge, and the exact binary fork theorem. The empty canonical interior-support worklist proves the exact row-span/subset certificate itself and rules out the concrete vertex-Kirchhoff evader branch. The all-interior/empty-worklist success side proves there is no odd closed walk in ambient interior support, while odd-worklist witnesses do not block synthesis once the concrete evader is excluded. The remaining burden is still to prove uniform exact CAP5 data reaches a terminal no-evader scheduler state, or to promote the residual scheduler branch edge by edge into certified control information or a genuine evader/worklist obstruction. | `<0.68,0.84>` | `[0.57,0.73]` | 92% |

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
- Repair-removal focused build archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-focused-build-20260629.log`.
- Validation lab JSON archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-lab-20260629.json`; the rerun
  contains 65 benchmark signatures, 65 projected-generator certificate
  reports/files, 80 mined survivor packets, and 80 rejected counterexample
  exports, with empty stderr.
- Axiom audit archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-axiom-audit-20260629.log`; the
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-full-build-20260629.log` with
  5900 jobs.
- New repair-removal theorem surface:
  `CAP5ExceptionalCyclicSeparatorRepairRealization`,
  `not_CAP5ExceptionalCyclicSeparatorRepairRealization_of_cyclicallyFiveEdgeConnected`,
  and
  `closedWalkExactShell_oneCollar_and_CAP5CyclicSeparatorRepair_obstruction`.
  These expose the fundamental small-cut obstruction for the CAP5/Jordan
  exceptional cyclic-separator surface: realizing even one compatible
  exceptional candidate as cyclic-cut data yields a cyclic edge cut of size at
  most four, hence is incompatible with cyclic five-edge-connectivity; the
  wrapper packages this with the exact-shell one-collar/canonical obstruction.
- Residual-classifier focused build archived locally as
  `fourcolor-move1-residual-classifier-focused-build-20260629.log`.
- Validation lab JSON archived locally as
  `fourcolor-move1-residual-classifier-lab-20260629.json`; the rerun contains
  65 benchmark signatures, 65 projected-generator certificate reports/files,
  80 mined survivor packets, and 80 rejected counterexample exports, with
  empty stderr.
- Axiom audit archived locally as
  `fourcolor-move1-residual-classifier-axiom-audit-20260629.log`; the new
  theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- New residual-classifier theorem surface:
  `closedWalkExactShell_oneCollar_and_CAP5GeneratorNode_residualClassifier`
  and
  `closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_residualClassifier`.
  These prove that a generated CAP5 separator node in a cyclically
  five-edge-connected graph cannot hide as a latent repair: it is missing
  primitive checker evidence or emits the outside-crossing edge outside its
  candidate support.  At report level, the 16-latent finite generator forces
  every counterexample latent exactly when the missing-evidence frontier is
  empty; otherwise Lean returns a concrete latent with missing checker
  evidence.  This is still a classifier, not the final Move-1 closure.
- Remaining Move-1 burden: prove the primitive missing-checker-evidence branch
  cannot occur for exact CAP5/Jordan shells, or reduce any such branch to the
  odd-walk obstruction, the realized small-cut obstruction, or the
  two-interior-edge face contradiction.

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
  `CAP5TransportedEdgeComponentCoverCore.enumeratedExceptionalAnnulusForcedEdgeClassifierBoundaryZeroControl_iff_no_boundaryZeroEvader`,
  `CAP5TransportedEdgeComponentCoverCore.enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryTargetClassifierControl_iff_no_targetEvader`.
  These prove that the emitted classifier coordinates control the full
  selected-boundary-zero carrier, any chosen boundary-zero Kirchhoff target, or
  the theorem-4.9 boundary target exactly when no nonzero chain in the
  corresponding carrier evades every enumerated CAP5 forced edge.
- Full boundary-zero no-evader closure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_no_missing_finsetControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`.
  These are the direct Move-2 no-evader/classifier-controls-boundary-zero step:
  a closed CAP5 checker plus absence of a nonzero selected-boundary-zero evader
  yields theorem-4.9 synthesis and proves that emitted CAP5 coordinates control
  the entire selected-boundary-zero subspace.
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
- Target-controlled odd-worklist fork focused build archived locally as
  `fourcolor-move2-target-odd-fork-focused-build-20260628.log`.
- Axiom audit archived locally as
  `fourcolor-move2-target-odd-fork-axiom-audit-20260628.log`; the two new
  theorem constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-target-odd-fork-strict-scans-20260628.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-target-odd-fork-full-build-20260628.log` with 5900 jobs.
- Target-controlled odd-worklist lab rerun archived locally as
  `fourcolor-move2-target-odd-fork-lab-20260628.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator
  certificate reports/files, 80 mined survivor packets, and 80 rejected
  counterexample exports.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- New target-controlled executable fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_oddInteriorWorklistEdge_of_closed_walk_odd_length_in_interiorSupport`.
  These consolidate the active F2 route surface: under target classifier
  control and an empty checker report, the executable fork is synthesis plus
  target coverage, or a concrete forced-edge-vanishing boundary-zero evader
  with nonzero theorem-4.9 boundary-vertex Kirchhoff sum and a decreasing
  remaining worklist edge.  If an odd closed walk lies in ambient interior
  support, the same theorem also exposes the remaining worklist edge
  unconditionally, so the exact shell cannot claim the empty-worklist subset
  certificate on that support.
- Empty-worklist no-odd focused build archived locally as
  `fourcolor-move2-empty-worklist-noodd-focused-build-20260628.log`.
- Axiom audit archived locally as
  `fourcolor-move2-empty-worklist-noodd-axiom-audit-20260628.log`; the three
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-empty-worklist-noodd-strict-scans-20260628.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-empty-worklist-noodd-full-build-20260628.log` with 5900
  jobs.
- Empty-worklist no-odd lab rerun archived locally as
  `fourcolor-move2-empty-worklist-noodd-lab-20260628.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate reports/files, 80 mined survivor packets, and 80 rejected
  counterexample exports.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- New success-branch odd-obstruction exclusion theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges`,
  `CAP5TransportedEdgeComponentCoverCore.interiorSupportForced_synthesis_and_boundaryTargetCoverage_and_no_closed_odd_walk`, and
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_synthesis_and_targetCoverage_and_no_closed_odd_walk`.
  These prove that the all-interior forced-edge/subset side excludes the odd
  closed-walk obstruction directly: if every ambient interior-support edge is
  enumerated as forced, there is no odd closed walk in ambient interior support.
  Consequently an empty canonical interior-support worklist reaches synthesis
  plus target coverage and simultaneously certifies that the odd-interior
  worklist obstruction is absent.
- New odd-interior no-evader closure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_and_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`.
  This proves that an odd closed walk can still leave the canonical
  interior-support worklist nonempty while the target-controlled no-evader
  branch closes theorem-4.9 synthesis and target coverage.  Therefore the odd
  worklist is only a measure/witness obstruction to the empty-worklist proof
  path, not a substitute for the genuine vertex-Kirchhoff evader branch.
- Report-forced-all lab rerun archived locally as
  `fourcolor-move2-report-forcedall-lab-20260629.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator certificate
  files, and 80 rejected counterexample exports.  The all-interior no-evader
  and vertex-Kirchhoff-failure-absent signatures are true on all 65 records;
  the declared-forced variants are true on the 36 forcing records.
- Report-forced-all focused detector build archived locally as
  `fourcolor-move2-report-forcedall-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-report-forcedall-axiom-audit-20260629.log`; the three new
  theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-report-forcedall-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-forcedall-full-build-20260629.log` with 5900 jobs.
- New report-forced-all theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_noEvader_of_forcedAllLatents`,
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorEmpty_synthesis_and_targetCoverage_of_forcedAllLatents`, and
  `CAP5TransportedEdgeComponentCoverCore.targetControlledSynthesis_or_evader_of_forcedAllLatents`.
  These replace the raw executable premise `missingCheckerEvidenceLatents = []`
  with the report verdict `forcedCounterexampleLatents = all`: if the
  generator forces all 16 latents under cyclic five-edge-connectivity, the
  branch feeds directly into the full selected-boundary-zero no-evader closure,
  the empty-worklist subset-certificate closure, or the target-controlled
  synthesis-versus-genuine-vertex-Kirchhoff-evader fork.
- Forced-all evader-fork lab rerun archived locally as
  `fourcolor-move2-forcedall-evaderfork-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Forced-all evader-fork focused detector build archived locally as
  `fourcolor-move2-forcedall-evaderfork-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-evaderfork-axiom-audit-20260629.log`; the two new
  theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-evaderfork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-evaderfork-full-build-20260629.log` with 5900
  jobs.
- New forced-all fork-half theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.targetControlledSynthesis_of_noEvader_of_forcedAllLatents`
  and
  `CAP5TransportedEdgeComponentCoverCore.targetControlledEvader_of_notSynthesis_of_forcedAllLatents`.
  These remove the last ambiguity in the report-forced-all target-controlled
  interface: under target classifier control, absence of the concrete
  theorem-4.9 boundary-vertex Kirchhoff evader proves synthesis plus target
  coverage, while failed synthesis proves the evader exists and carries a
  decreasing remaining-worklist edge.  This is an interface decision, not yet
  the exact-shell proof of the no-evader/subset side.
- Forced-all payload-fork lab rerun archived locally as
  `fourcolor-move2-forcedall-payloadfork-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Forced-all payload-fork focused detector build archived locally as
  `fourcolor-move2-forcedall-payloadfork-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-payloadfork-axiom-audit-20260629.log`; the two
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-payloadfork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-payloadfork-full-build-20260629.log` with 5900
  jobs.
- New forced-all canonical payload theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.canonicalPayloadEvader_of_notSynthesis_of_forcedAllLatents`
  and
  `CAP5TransportedEdgeComponentCoverCore.synthesis_or_canonicalPayloadEvader_of_forcedAllLatents`.
  These sharpen the forced-all failure side from an existential evader into
  the finite path-xor artifact the lab is meant to return: detector payload,
  boundary-zero chain, non-forced remaining interior edge with nonzero chain
  value, strict worklist decrease, and nonzero canonical red/blue family
  pairing.  This still leaves the exact-shell no-evader/subset derivation open.
- Forced-all pure-evader lab rerun archived locally as
  `fourcolor-move2-forcedall-pureevader-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Forced-all pure-evader focused detector build archived locally as
  `fourcolor-move2-forcedall-pureevader-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-pureevader-axiom-audit-20260629.log`; the two
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-pureevader-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-pureevader-full-build-20260629.log` with 5900
  jobs.
- New forced-all pure-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_notSynthesis_of_forcedAllLatents`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`.
  These state the F2 fork at the no-target level: once the report forces all
  latents, failed synthesis is already a genuine selected-boundary-zero evader
  for the enumerated forced edges, with the decreasing worklist edge attached.
  Target-control and canonical payload theorems are now refinements of this
  pure evader branch.
- Forced-all oracle-fork focused detector build archived locally as
  `fourcolor-move2-forcedall-oraclefork-focused-build-20260629.log`.
- Forced-all oracle-fork lab rerun archived locally as
  `fourcolor-move2-forcedall-oraclefork-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-oraclefork-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-oraclefork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-oraclefork-full-build-20260629.log` with 5900
  jobs.
- New forced-all oracle theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroEvader_of_forcedAllLatents`.
  This packages the F2 oracle itself: under the executable forced-all report,
  either no-evader closes theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control, or there is a concrete nonzero selected-boundary-zero
  evader for the enumerated forced edges.  The exact-shell task remains to
  prove which side uniform CAP5/Jordan shell data supplies.
- Empty-worklist no-evader lab rerun archived locally as
  `fourcolor-move2-emptyworklist-noevader-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Empty-worklist no-evader focused detector build archived locally as
  `fourcolor-move2-emptyworklist-noevader-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-emptyworklist-noevader-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-emptyworklist-noevader-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-emptyworklist-noevader-full-build-20260629.log` with 5900
  jobs.
- New empty-worklist no-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents`.
  This upgrades the forced-all empty-worklist/subset certificate: empty
  canonical interior-support worklist now proves the actual no-evader verdict,
  theorem-4.9 synthesis, and full selected-boundary-zero classifier control.
  The remaining algebraic task is to prove uniform exact CAP5/Jordan shell data
  reaches this empty-worklist branch, or to formalize the evader/worklist
  alternative.
- Forced-all scheduler focused detector build archived locally as
  `fourcolor-move2-forcedall-scheduler-focused-build-20260629.log`.
- Forced-all scheduler lab rerun archived locally as
  `fourcolor-move2-forcedall-scheduler-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-scheduler-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-scheduler-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-scheduler-full-build-20260629.log` with 5900
  jobs.
- New forced-all scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_or_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`.
  This packages the residual finite obligation after the executable forced-all
  report: either the empty canonical interior-support worklist gives
  no-evader/synthesis/full-control, or a concrete remaining interior-support
  edge is available with strict erasure decrease.  Uniform exact shell data now
  has to prove the left side or use the returned edge to drive the scheduler.
- Forced-all residual-scheduler focused detector build archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-focused-build-20260629.log`.
- Forced-all residual-scheduler lab rerun archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-lab-20260629.json`; stderr is
  empty, and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-full-build-20260629.log` with
  5900 jobs.
- New forced-all residual-scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlTraceEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_finsetControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_forcedAllResidualSchedulerPayloadEvader_of_forcedAllLatents`.
  These strengthen the failure side from a bare remaining-edge erasure witness
  into a processed-state scheduler payload: complete `(0, 0, 16)` checker
  histogram, forced-bin detector, selected-boundary-zero evader, traced
  remaining interior-support edge, residual-worklist membership, strict
  residual decrease after `insert e processed`, strict canonical erasure
  decrease, and nonzero canonical red/blue family pairing.
- Forced-all residual-transition focused detector build archived locally as
  `fourcolor-move2-forcedall-residual-transition-focused-build-20260629.log`.
- Forced-all residual-transition lab rerun archived locally as
  `fourcolor-move2-forcedall-residual-transition-lab-20260629.json`; stderr is
  empty, and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-residual-transition-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-residual-transition-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-residual-transition-full-build-20260629.log` with
  5900 jobs.
- New forced-all residual-transition theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_forcedAllResidualSchedulerTransitionEvader_of_forcedAllLatents_of_processedControl`.
  This strengthens the scheduler failure branch again: under a processed-edge
  zero invariant, failed synthesis returns the same selected-boundary-zero
  evader and residual decrease, plus a proof that the selected edge is not
  controlled by the immutable classifier output and the exact one-edge
  emitted/control update needed to insert it into the processed state.
- Terminal residual scheduler focused detector build archived locally as
  `fourcolor-move2-residual-terminal-focused-build-20260629.log`.
- Terminal residual scheduler lab rerun archived locally as
  `fourcolor-move2-residual-terminal-lab-20260629.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator certificate
  files, and 80 rejected counterexample exports.  The all-interior no-evader
  and vertex-Kirchhoff-failure-absent signatures are true on all 65 records;
  the declared-forced variants are true on the 36 forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-residual-terminal-axiom-audit-20260629.log`; the two new
  theorem constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-residual-terminal-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-residual-terminal-full-build-20260629.log` with 5900 jobs.
- New terminal residual scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_of_residualRemainingInteriorSupportEmpty_of_processedControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.residualRemainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents_of_processedControl`.
  These close the success endpoint for the finite scheduler: residual
  exhaustion plus the processed-control invariant proves no selected-boundary-zero
  evader exists, and under the forced-all report yields theorem-4.9 synthesis
  with full selected-boundary-zero classifier control.
- Failed-terminal scheduler focused detector build archived locally as
  `fourcolor-move2-failed-terminal-step-focused-build-20260629.log`.
- Failed-terminal scheduler lab rerun archived locally as
  `fourcolor-move2-failed-terminal-step-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, 80 rejected counterexample exports, 80 mined rejections,
  and 80 mined survivors.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-failed-terminal-step-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-failed-terminal-step-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-failed-terminal-step-full-build-20260629.log` with 5900
  jobs.
- New failed-terminal scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_residualSchedulerStep_of_notSynthesis_of_forcedAllLatents_of_processedControl`.
  This combines the terminal theorem and the residual transition into the
  decision form needed by the scheduler: under forced-all and the
  processed-control invariant, failed synthesis implies the residual worklist
  is nonempty and returns a genuine selected-boundary-zero evader, the next
  residual edge, proof that the edge is not controlled by the immutable
  classifier output, the one-edge emitted/control update, and strict residual
  decrease.
- Immutable-scheduler obstruction focused detector build archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-focused-build-20260629.log`.
- Immutable-scheduler obstruction lab rerun archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-lab-20260629.json`; stderr
  is empty, and the run contains 65 benchmark signatures, 65
  projected-generator certificate files, 80 rejected counterexample exports,
  80 mined rejections, and 80 mined survivors.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-full-build-20260629.log`
  with 5900 jobs.
- New immutable-scheduler obstruction theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_immutableProcessedControlObstruction_of_notSynthesis_of_forcedAllLatents_of_processedControl`.
  This lifts the lower-level immutable-processed obstruction to the
  route-facing forced-all branch: the residual edge returned by failed
  synthesis cannot be inserted into `processed` using the original classifier
  output.  The scheduler must add the one-edge emitted/control update or keep
  the evading boundary-zero chain as the genuine obstruction.
- Residual scheduler route-decision focused detector build archived locally as
  `fourcolor-move2-residual-scheduler-route-decision-focused-build-20260629.log`.
- Residual scheduler route-decision lab rerun archived locally as
  `fourcolor-move2-residual-scheduler-route-decision-lab-20260629.json`;
  stderr is empty, and the run contains 65 benchmark signatures, 65
  projected-generator certificate files, 80 rejected counterexample exports,
  80 mined rejections, and 80 mined survivors.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- New residual scheduler route-decision theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.residualSchedulerTerminalNoEvader_or_synthesis_or_immutableProcessedControlObstruction_of_forcedAllLatents_of_processedControl`.
  This packages the finite scheduler state: terminal residual exhaustion closes
  no-evader/synthesis/control, synthesis may already be closed before terminal
  exhaustion, and the remaining branch returns a genuine evader plus the next
  promoted edge with immutable processing ruled out and strict residual
  decrease.

## Remaining Completion Requirements

- Move 1: prove primitive missing-checker evidence cannot occur for exact
  CAP5/Jordan shells, or reduce that branch to the odd-walk obstruction, the
  cyclic-five small-cut repair-removal obstruction, or the closed-walk
  exact-shell two-interior-edge face contradiction.
- Move 2: derive the no-evader/subset certificate from the uniform CAP5 shell
  data by reaching the terminal residual scheduler success theorem, or iterate
  the route-decision theorem by promoting each selected edge with new certified
  control information.  Immutable processing of that edge is formally ruled
  out; if promotion cannot be certified, formalize the genuine
  vertex-Kirchhoff/path-xor evader produced by failure of that certificate.
  The no-evader direction now already gives full selected-boundary-zero
  classifier control and synthesis, and the success side carries the
  no-odd-interior certificate.
- Before any public checkpoint: strict proof-marker scan, trusted-constant audit for new
  theorems, validation lab rerun, full `lake -f lakefile.lean build
  Mettapedia`, and push only to `origin/fourcolor/cont-20260626`.
