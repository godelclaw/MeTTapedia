# FourColor: goal, status, and how to approach it

*Last restructured: 2026-06-10.  Last proof-state update: 2026-06-28.  This file replaces the 3,577-line
`Theorem49NextHardProblemSummary.lean` prose (now in `Legacy/`) as the
entry point.*

## The goal

By Tait's classical reduction, the Four Color Theorem is equivalent to: every
bridgeless cubic planar graph has a proper 3-edge-coloring
(`IsTaitEdgeColoring`).  Goertzel's v23 manuscript attacks this via an
inductive boundary argument whose load-bearing step is **Theorem 4.9**: an
F₂-algebraic synthesis (`Theorem49BoundaryRootSynthesis`) saying the
boundary-zero Kirchhoff subspace is spanned by projected Kempe-closure
generators on a plane embedding with boundary.  This development is the formal
audit and (attempted) formalization of that step.

Read these three files first — they are the whole live surface:

| File | Contents |
|---|---|
| `Goal.lean` | The target (`Theorem49ShellClaim`), its reduction to four geometric oracles plus a fifth non-geometric algebraic cancellation oracle, and proofs that **all four geometric uniform oracles are false** — including the v23.5 residual/current-boundary lane, whose positive wrapper is fixed-embedding equivalent to the refuted collar-layer surface |
| `Shells.lean` | Bundled hypothesis packages (`ClosedWalkExactShell`, `SuccessorCycleExactShell`, `ClosedWalkCancellationShell`, …) replacing the historical 8–10-hypothesis telescopes |
| `Frontier.lean` | The maximal positive and negative results, stated over the bundles as thin wrappers, including detector-based cancellation sufficiency |

## Current status (one paragraph)

The positive lane is complete from geometry upward: repaired previous-boundary
witness geometry, explicit well-founded peel-witness data, or generic
interior-dual distance-peel data on the shell's embedding each yield full
`Theorem49BoundaryRootSynthesis` (`Frontier.lean`, wrapping the route files).
The same file now also exposes a non-geometric positive lane: an exact shell
plus the projected-generator detector certificate
(`BoundaryZeroProjectedGeneratorDetector`) also yields full synthesis, and
`Goal.lean` now packages both the old whole-closure uniform hypothesis
`AlgebraicCancellationOracle` and the weaker, lab-faithful
`AlgebraicNeighborhoodCancellationOracle`, which only asks for some explicit
detecting coloring family inside the shell Tait coloring's edge-Kempe closure.
The live shell/frontier surface now also carries the direct kernel-check form
of that same obligation: `Shells.lean` bundles exact shells together with an
explicit family whose concrete pairing map has trivial kernel, `Frontier.lean`
proves that this already yields full theorem-4.9 synthesis, and `Goal.lean`
packages the corresponding uniform hypothesis as
`AlgebraicNeighborhoodPairingKernelOracle`.
The negative lane is complete from the shells downward: the
wheel-with-inner-triangle and shared-interior-pair benchmarks inhabit the full
endpoint-bearing exact one-collar/v23 shells while refuting every named
geometric layer, so no uniform derivation from the manuscript's stated
hypotheses to the geometry its argument consumes can exist
(`Goal.lean: not_interiorDualPeelOracle, not_wellFoundedPeelOracle,
not_previousBoundaryGeometryOracle, not_residualBoundaryGeometryOracle`).
The last of these is the formal verdict on the v23.5 revision memo's repair
proposal: the residual/current-boundary lane as currently specified is
conservative over the refuted collar-layer surface, so only its unformalized
"algebraic cancellation certificate" obligation remained live in prose.  The
new live-surface files now formalize that obligation directly as the shell-wise
detector oracles above: it is no longer just roadmap prose, but unlike the
geometric oracles it is not presently refuted by the current shell-bearing
benchmarks.  Moreover, the new file
`Mettapedia/GraphTheory/FourColor/Theorem49ColoringGeneratorFamilyRoute.lean`
proves that a detector on any explicit coloring family inside the base
edge-Kempe closure already upgrades to the full theorem-4.9 synthesis
endpoint.  So the live non-geometric lane no longer has to be phrased as a
whole-closure detector; it can match the finite lab's smaller explicit
neighborhood certificates directly.  A new kernel-checked theorem now sharpens
the comparison:
`Theorem49DetectorStrength.lean` proves that on every shell-bearing embedding
the theorem-4.9 target `W₀(H)` is a proper subspace of the full
selected-boundary-zero chain space.  So the detector/cancellation oracle is
strictly stronger than the manuscript target on the current shell surface; it
is not merely a restatement of theorem 4.9 in different words.  Structurally, any shell with an
unblocked endpoint forces two distinct interior edges on some face boundary
(`Frontier.lean`), which is what kills the facewise-at-most-one,
canonical-choice, and source-preserving one-collar repair lanes.  Update
2026-06-11: the new finite lab under `scripts/4cp_lab/` directly decides the
current endpoint on the small explicit benchmarks.  It reproduces the positive
degenerate wheel and diamond-with-triangle cases, and finds
`Theorem49BoundaryRootSynthesis` true on the shell-bearing
`wheelWithInnerTriangleEmbedding` and `sharedInteriorPairAnnulusEmbedding` for
their explicit benchmark colorings; on the same embeddings it is also true for
all 36 wheel Tait colorings and all 72 shared-interior-pair Tait colorings
enumerated by the lab.  A follow-up detector experiment now localizes the
annihilator burden further: for the wheel benchmark, the explicit coloring
alone already kills every selected-boundary-zero annihilator, while for the
shared-interior-pair benchmark the explicit coloring plus its six one-step
Kempe neighbors already suffice.  The wheel explicit-coloring case is now
kernel-checked in Lean by
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelEndpointRegression.lean`,
and `Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelFullSweepRegression.lean`
now upgrades that explicit endpoint to all 36 wheel Tait colorings.  The
shared-interior-pair benchmark now has kernel-checked representatives for both
of the 36-color Kempe-closure classes found by the lab, via
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairEndpointRegression.lean`
and
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairSecondClosureEndpointRegression.lean`.
The new file
`Mettapedia/GraphTheory/FourColor/Theorem49SynthesisClosureInvariance.lean`
then proves that the full theorem-4.9 synthesis package depends only on the
underlying `EdgeKempeClosure` class of the base coloring, and can be
transported along mutual edge-Kempe reachability.  So the remaining Lean gap
on the current pathologies is no longer the wheel sweep, no longer a missing
shared representative, and no longer the shared class-membership /
classification step either: the new file
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairFullSweepRegression.lean`
now classifies every Tait coloring of the shell-bearing shared benchmark into
two parametric Kempe-closure families, proves four generic closure generators
per family, reduces each family to its explicit kernel-checked representative,
and upgrades theorem 4.9 to all 72 shared Tait colorings.  So the current
explicit shell-bearing benchmarks no longer leave a Lean gap at the level of
their full finite Tait sweeps; the remaining open burden on this path is
either a wider shell-bearing search or a new general computable F₂ layer that
scales beyond these two benchmarks.  Update later on 2026-06-11: the new file
`Mettapedia/GraphTheory/FourColor/Theorem49BoundaryProjectionDetector.lean`
shows that the selected-boundary projected-generator detector property is also
an edge-Kempe-closure invariant, and the wheel/shared full-sweep regression
files now upgrade not only `Theorem49BoundaryRootSynthesis` but also that
detector property to all 36 wheel and all 72 shared Tait colorings.  So the
current finite benchmarks are now closed in Lean at the detector layer as
well, not only at the final theorem-4.9 synthesis package.  Update later still
on 2026-06-11: the exact wheel radius-0 detector certificate exposed by the
finite lab is now kernel-checked directly in
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelRadiusZeroDetectorRegression.lean`,
showing that the explicit wheel coloring alone already detects every nonzero
selected-boundary-zero chain.  The exact shared radius-1 detector certificate
is now kernel-checked directly in
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairRadiusOneDetectorRegression.lean`.
So the finite lab's two minimal explicit detector certificates are both now
Lean-native.  Moreover, Lean sharpens the lab's seven-color shared radius-1
neighborhood: for the shared explicit benchmark coloring, the detector already
follows from a two-color witness subfamily consisting only of the base coloring
and one inner red/blue Kempe neighbor.

Update 2026-06-28: the live continuation branch now treats the old geometric
repair sequence as a fork to decide, not a place to bank more isolated packets.
The validation lab run archived locally as
`fourcolor-move2-f2-oracle-validation-lab-20260628.log`
found no top-level all-interior or declared/forcing-control F2 evader across
65 records, and the crux report still rejects the outside-crossing geometric
route on generated two-band annuli.  In Lean,
`CAP5PathXorDetector.lean` now exposes the target-level no-evader contract
`forcedEdgeBoundaryTargetCoverage_iff_no_targetEvader` and the Move-2 handoff
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_no_evader_of_no_missing_finsetControl`:
a completed CAP5 finite checker with no selected-boundary-zero evader closes
`Theorem49BoundaryRootSynthesis` and also proves forced-edge coverage of the
actual theorem-4.9 target `W0(H)`.  This advances the algebraic fork but does
not decide it uniformly; the remaining work is to derive the full no-evader
verdict from exact shell data or exhibit a genuine evader outside the current
finite sample.

Later on 2026-06-28: the all-interior Move-2 survivor is now route-facing in
Lean rather than only a lab observation.  The rerun archived locally as
`fourcolor-move2-interior-frontier-validation-lab-20260628.log` again saw
65 records and the algebraic-F2 implication
`forcing_interior_edges_nonempty => f2_all_interior_boundary_zero_only_no_evader`
survived with support 36 and purified support 18.  The new CAP5 detector
theorems `interiorSupportForced_synthesis_and_boundaryTargetCoverage` and
`interiorSupportForced_or_remainingEdge` say: if the closed primitive checker
has enumerated every ambient interior-support edge as forced, then theorem-4.9
synthesis and forced-edge coverage of `W0(H)` both follow; otherwise the
canonical interior-support worklist exposes a concrete remaining edge with a
strictly smaller erasure measure.  This converts the surviving F2 lane into a
success-or-next-edge frontier, but still leaves the uniform enumeration
problem open.

Later still on 2026-06-28: the same all-interior lane now has an executable
closed-worklist certificate.  The rerun archived locally as
`fourcolor-move2-empty-worklist-validation-lab-20260628.log` again confirmed
the finite F2 all-interior survivor on 65 records.  In Lean,
`remainingInteriorSupportEmpty_synthesis_and_targetCoverage` and
`remainingInteriorSupportEmpty_report_synthesis_and_targetCoverage` say that
an empty canonical interior-support worklist, together with the closed
primitive checker report, directly yields theorem-4.9 synthesis and forced-edge
coverage of `W0(H)`.  The remaining algebraic burden is now sharper: prove the
exact CAP5 shell reaches this empty worklist uniformly, or formalize the
remaining worklist edge as the genuine obstruction/evader source.

Subsequently on 2026-06-28: the closed executable report failure branch was
made route-facing.  In Lean,
`boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl`
and
`theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`
say that, once the primitive checker report is empty, a failed synthesis run
does not merely leave an abstract gap: it carries a genuine
selected-boundary-zero evader for the enumerated forced edges and a concrete
remaining interior-support edge with a decreasing worklist measure.  This
sharpens the algebraic fork to synthesis versus evader-plus-next-edge; it still
does not prove the exact CAP5 shell uniformly chooses the synthesis side.

After the fork-decision reset on 2026-06-28: the classifier/no-evader oracle is
now expressed as an exact Lean equivalence rather than only a sufficient
handoff.  The lab artifact
`fourcolor-move2-classifier-noevader-lab-20260628.json` records 65 benchmark
signatures: both all-interior F2 no-evader flags are true on all 65 records,
and both declared-forced no-evader flags are true on the 36 records with
nonempty forcing interior edges.  The exported projected-generator bundle
contains 65 certificate files and 80 rejected counterexample files; the two
algebraic-F2 cruxes still survive with support 36 and purified support 18.
In Lean,
`enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader`
and
`theorem49BoundaryTargetClassifierControl_iff_no_targetEvader` say that the
emitted CAP5 classifier coordinates control the boundary-zero Kirchhoff target,
and the theorem-4.9 target `W0(H)`, exactly when no nonzero target chain evades
every enumerated CAP5 forced edge.  This does not decide the exact shell, but
it removes the algebraic ambiguity in the oracle statement: the remaining
Move-2 fork is now to prove that exact CAP5 data supplies the no-evader side,
or to exhibit the evader.

The next target-level corollary turns finite dimension into an explicit fork
test for exact CAP5 data.  In Lean,
`exists_theorem49BoundaryTargetEvader_of_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_lt`
says that a CAP5 classifier below the boundary-zero plus theorem-4.9 Kirchhoff
target dimension bound yields a genuine nonzero `W0(H)` evader for the
enumerated forced edges.  Conversely,
`edge_card_le_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_of_no_targetEvader`
says any no-evader classifier must pay that lower bound.  This does not prove
exact shell no-evader, but it makes the finite F2 fork executable: exact shell
data must either meet the target dimension budget or produce the evader branch.

The latest Move-2 bridge separates the target oracle from the remaining
boundary-zero obstruction.  In Lean,
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_offTargetBoundaryZeroEvader_of_no_missing_finsetControl`
says target classifier control closes the completed CAP5 checker exactly when
there is no off-target selected-boundary-zero evader.  Conversely,
`offTargetBoundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`
says a closed-checker failure under target control produces such an off-target
evader together with the decreasing interior-support worklist edge.  The
remaining algebraic fork is now explicit: prove exact CAP5 data excludes these
off-target evaders, or formalize one.

That off-target branch is now concrete rather than merely complementary.  Lean
proves
`CAP5TransportedEdgeComponentCoverCore.exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget`:
any selected-boundary-zero chain outside `W0(H)` fails a Kirchhoff equation at
some theorem-4.9 boundary vertex.  The route-facing versions
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl`
and
`boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`
therefore replace the abstract off-target fork by a concrete vertex-Kirchhoff
failure fork: exact shell data must either rule out forced-edge-vanishing
boundary-zero chains with a nonzero theorem-4.9 boundary-vertex Kirchhoff sum,
or exhibit one.

The vertex-failure fork now has the same lab-to-Lean interface as the target
oracle.  The finite F2 lab reports the additive signature
`f2_all_interior_boundary_zero_kirchhoff_failure_absent`: on the 65-record
2026-06-28 rerun it is true for every all-interior control set, and the crux
packet
`forcing_edges_to_f2_all_interior_boundary_zero_kirchhoff_failure_absent`
survives on the 36 records with nonempty forcing interior edges.  In Lean,
`no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`
turns the row-span/subset certificate into the no-failure hypothesis, while
`boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`
turns failure of that certificate into a genuine evader.  The route-facing
closure theorem
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl`
therefore makes the remaining algebraic obligation precise: prove the exact
shell subset certificate, or formalize the evader produced by its failure.
Lean now also records the equivalence
`forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
and the route-facing binary theorem
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl_of_no_missing_finsetControl`:
under target classifier control and a closed checker, the subset certificate
closes synthesis/target coverage, while failure of the certificate is already
the genuine vertex-Kirchhoff evader.  The next mathematical step is therefore
not another interface theorem; it is the exact shell subset certificate itself,
or a formalized counterexample to it.

The exact subset certificate is now proved on the executable empty-worklist
shell.  Lean has
`interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty`,
`forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_interiorEdgeSupport_subset_enumeratedForcedEdges`,
`forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty`,
`no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_remainingInteriorSupportEmpty`,
and
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_remainingInteriorSupportEmpty_of_no_missing_finsetControl`.
Thus an empty canonical interior-support worklist no longer just closes the old
no-evader route; it proves the row-span/subset certificate demanded by the
current binary fork and rules out the concrete vertex-Kirchhoff evader branch.
The remaining fork decision is narrower: prove exact CAP5 data reaches this
empty-worklist/subset side uniformly, or formalize the evader exposed when it
does not.

On the geometric fork, the source-bound one-collar repair treadmill has now
been consolidated into a shell-level obstruction.  In
`FrontierGeometric.lean`, the theorems
`not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell`,
`not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell`, and
`not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell`
show that every closed-walk exact shell blocks the canonical witness choice
and all one-collar collar/previous-boundary witness geometries for the same
reason: the shell's unblocked endpoint already forces a face with two distinct
interior-support edges.  This is no longer a single failing packet; it is a
uniform obstruction for the canonical/one-collar positive-collar repair class.
The side-cut part now has the same structural treatment for the odd-walk
separator class: `not_exists_sideCut_crosses_closed_odd_walk_subset` and
`not_exists_exceptionalAnnulusCrossingOutsideEdge_of_closed_odd_walk_subset`
say that any finite side-cut support containing an odd closed walk cannot be
realized by a single vertex-side predicate, nor by the CAP5 exceptional
outside-crossing normal form.  The consolidated wrappers
`closedWalkExactShell_oneCollar_and_oddSideCut_obstruction` and
`closedWalkExactShell_oneCollar_and_CAP5OddSideCut_obstruction` package this
with the shell-wide one-collar obstruction.  The remaining geometric work is
to prove that the residual side-cut/cyclic-separator surface always exposes
such an odd-walk support or reduces to the two-interior-edge face
contradiction, and then push the result through repair-removal.

## The open problem

Exactly two route forks are live; isolated repair-packet refutations are no
longer acceptable progress.

1. **Geometric fork**: consolidate the repaired CAP5/Jordan failures into a
   single structural obstruction theorem.  The source-bound
   canonical/one-collar part is now shell-wide: closed-walk exact shells force
   the same two-interior-edge face obstruction against canonical witness
   choice, one-collar collar geometry, and one-collar previous-boundary
   witness geometry.  The side-cut part is now structural for supports
   containing an odd closed walk: those supports cannot realize a cyclic
   separator by a single vertex side, including in the CAP5 outside-crossing
   normal form.  The remaining Move-1 gap is to prove the residual
   side-cut/cyclic-separator layer necessarily has that odd-walk support or
   reduces to the face obstruction, and then carry the theorem through
   repair-removal.
2. **Algebraic fork**: resolve the F2 cancellation oracle.  The current
   machine-checked statement is sharper than a one-way handoff: classifier
   control of the theorem-4.9 target is equivalent to absence of a nonzero
   enumerated-forced-edge evader; underdimensioned classifiers produce a
   genuine target evader; full no-evader plus the closed finite checker
   implies theorem-4.9 synthesis and target coverage; and target classifier
   control reduces the remaining failure branch to a forced-edge-vanishing
   selected-boundary-zero evader with a concrete theorem-4.9 boundary-vertex
   Kirchhoff failure, plus a decreasing worklist edge; and the row-span/subset
   bridge says the exact remaining certificate is that every forced-vanishing
   boundary-zero chain lies in the theorem-4.9 target.  The empty-worklist shell
   now proves that exact subset certificate and eliminates the concrete
   vertex-Kirchhoff evader branch there.  The exact binary theorem packages the
   uniform route as synthesis/target coverage or a genuine evader.  The
   remaining crux is whether exact shell/CAP5 data proves that subset
   certificate uniformly, or whether a genuine vertex-Kirchhoff failure evader
   exists.

The historical trichotomy below remains useful background:

1. **Repair**: find same-embedding geometric hypotheses that (a) are
   natural for the manuscript's induction, (b) are *not* satisfied by the
   wheel/shared-interior-pair benchmarks, and (c) construct one of the four
   oracle inputs.  Everything at or below the exact shells is proven
   insufficient; candidate hypotheses must be checked against the benchmarks
   *first* (5-minute check) before building route surface (multi-day work).
2. **Non-geometric repair**: derive the new shell-wise detector obligation
   `AlgebraicNeighborhoodCancellationOracle` uniformly from the exact shell,
   or at least derive the stronger whole-closure
   `AlgebraicCancellationOracle`.  This is the formalized version of the
   memo's algebraic cancellation certificate: it is strong enough to imply
   `Theorem49ShellClaim`, it now matches the finite lab's explicit
   certificates at the right granularity, and the direct kernel-check shell
   form `AlgebraicNeighborhoodPairingKernelOracle` now packages those
   certificates before any upgrade to the detector surface.  The current wheel/shared
   benchmark families no longer refute it.
3. **Refute**: find a shell-bearing embedding where
   `Theorem49BoundaryRootSynthesis` itself fails.  The cheapest current
   candidates have now been checked computationally: the finite lab in
`scripts/4cp_lab/exp01_wheel_endpoint.py` finds the synthesis **true** on
the shell-bearing wheel and shared-interior-pair benchmarks, both for the
explicit benchmark colorings and for every Tait coloring the lab enumerates
there.  The companion detector experiment
`scripts/4cp_lab/exp02_kempe_detector.py` shows the remaining explicit
annihilator checks are tiny: radius `0` for the wheel and radius `1` for
the shared-interior-pair case.  Both exact certificates are now
kernel-checked directly in Lean: the wheel singleton radius-0 certificate, and
the shared radius-1 certificate, which even compresses there to a two-color
witness subfamily.  So the direct-counterexample lane survives only through a
different shell-bearing benchmark, or through a future Lean-computable F₂
elimination/search layer that scales beyond the wheel and shared-interior-pair
benchmarks already discharged in Lean.

## File organization

- **`Goal.lean`, `Shells.lean`, `Frontier.lean`** — the live surface (above).
- **Core theory** (reusable, Mathlib-style): `ColorAlgebra`, `FaceIncidence`,
  `PlanarFaceIncidence`, `Orthogonality`, `BoundaryVanishing`,
  `Theorem49LinearAlgebra`, the `PlanarBoundary*` family (embeddings,
  sources, annulus construction, peeling), `Theorem49KempeGeneratorSpan`,
  `Theorem49SpanningGap`.
- **Route files** (`Theorem49*Route`, `Theorem49Synthesis`,
  `Theorem49PositiveGeometricSource*`, …): the positive lane.  Heavily
  duplicated between closed-walk and successor-cycle presentations; new
  statements should go through `Shells.lean` bundles instead of extending
  these.
- **Load-bearing benchmark/obstruction files kept in the main tree** (they
  are imported by route files): `Theorem49AtMostOneNonemptyCarrierImpossibility`,
  `Theorem49ForcingInteriorEdgeObstruction`,
  `Theorem49InteriorVerticesEndpointObstruction`,
  `Theorem49PositiveGeometricSourceImpossibility`, and the four
  `Theorem49PlanarBoundaryAnnulus*Regression` keepers (these define the
  shared-interior-pair benchmark).
- **`Legacy/`**: the historical obstruction ledger plus the concrete explicit
  endpoint regression certificates.  Fully verified.  Its maximal results are
  re-exported by `Frontier.lean`; weaker shells refuted there are subsumed a
  fortiori.  Do not add new shell-obstruction wrappers there; do not build on
  it except through `Frontier`.

## Conventions going forward

- State new theorems over the `Shells.lean` bundles.  If a hypothesis package
  recurs three times, bundle it.
- No new 100+-character theorem names; the shell vocabulary exists so names
  can be short.
- A failed universal converse is one application of
  `not_forall_target_of_exists_shell_witness` to an explicit witness — do not
  write bespoke 60-line converse theorems.
- New benchmark counterexamples get their own file with the benchmark's facts
  proved once; obstruction theorems combine benchmark facts with shell
  definitions.
- Keep the tree without proof placeholders or extra trusted constants.

## Build targets

- Live surface: `lake build Mettapedia.GraphTheory.FourColor.Goal`
  (pulls in `Shells`, `Frontier`, and the route files they wrap).
- Everything incl. ledger: `lake build Mettapedia.GraphTheory.FourColorRegression`.
- Dependency audit: `python3 ../../../scripts/lean_deps.py <path>`.
