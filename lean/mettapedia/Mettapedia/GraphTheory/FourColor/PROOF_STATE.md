# FourColor Proof State

Last updated: 2026-06-28 on `fourcolor/cont-20260626`.

This file tracks the two active route forks.  The Four Color Theorem is not
claimed here; the target is a decided state for the Goertzel theorem-4.9 route.

## Fork State

| Fork | State | PLN STV | ITV | Progress |
|---|---|---:|---:|---:|
| Geometric CAP5/Jordan repair | Multiple repairs are refuted; still missing the single structural obstruction theorem that retires the fork. | `<0.42,0.60>` | `[0.25,0.65]` | 62% |
| Algebraic F2 cancellation oracle | Lab finds no top-level all-interior/declared forced-edge evader on 65 records; Lean now proves full no-evader + closed checker gives synthesis and target coverage, promotes the all-interior survivor to a success-or-remaining-edge frontier, exposes an executable empty-worklist certificate, and makes the closed-report failure branch a genuine F2 evader plus a remaining worklist edge. Uniform no-evader from exact shell data is not yet proved. | `<0.38,0.66>` | `[0.25,0.59]` | 62% |

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

## Remaining Completion Requirements

- Move 1: prove a single fundamental obstruction for the repaired
  CAP5/Jordan geometric class, not another isolated repair-packet failure.
- Move 2: either prove that the exact shell/CAP5 classifier always supplies
  the full forced-edge no-evader verdict needed by the synthesis handoff, or
  exhibit and formalize a genuine evader.
- Before any public checkpoint: strict proof-marker scan, trusted-constant audit for new
  theorems, validation lab rerun, full `lake -f lakefile.lean build
  Mettapedia`, and push only to `origin/fourcolor/cont-20260626`.
