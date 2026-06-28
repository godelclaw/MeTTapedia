# FourColor Proof State

Last updated: 2026-06-28 on `fourcolor/cont-20260626`.

This file tracks the two active route forks.  The Four Color Theorem is not
claimed here; the target is a decided state for the Goertzel theorem-4.9 route.

## Fork State

| Fork | State | PLN STV | ITV | Progress |
|---|---|---:|---:|---:|
| Geometric CAP5/Jordan repair | Multiple repairs are refuted; still missing the single structural obstruction theorem that retires the fork. | `<0.42,0.60>` | `[0.25,0.65]` | 62% |
| Algebraic F2 cancellation oracle | Lab finds no top-level all-interior/declared forced-edge evader on 65 records; Lean now proves full no-evader + closed checker gives synthesis and target coverage. Uniform no-evader from exact shell data is not yet proved. | `<0.34,0.64>` | `[0.22,0.58]` | 58% |

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

## Remaining Completion Requirements

- Move 1: prove a single fundamental obstruction for the repaired
  CAP5/Jordan geometric class, not another isolated repair-packet failure.
- Move 2: either prove that the exact shell/CAP5 classifier always supplies
  the full forced-edge no-evader verdict needed by the synthesis handoff, or
  exhibit and formalize a genuine evader.
- Before any public checkpoint: strict proof-marker scan, trusted-constant audit for new
  theorems, validation lab rerun, full `lake -f lakefile.lean build
  Mettapedia`, and push only to `origin/fourcolor/cont-20260626`.
