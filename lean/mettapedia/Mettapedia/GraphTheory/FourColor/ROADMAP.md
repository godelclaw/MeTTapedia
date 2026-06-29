# FourColor: goal, status, and how to approach it

*Last restructured: 2026-06-10.  Last proof-state update: 2026-06-29.  This file replaces the 3,577-line
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

Read these four files first — they are the whole live surface:

| File | Contents |
|---|---|
| `Goal.lean` | The target (`Theorem49ShellClaim`), its reduction to four geometric oracles plus a fifth non-geometric algebraic cancellation oracle, and proofs that **all four geometric uniform oracles are false** — including the v23.5 residual/current-boundary lane, whose positive wrapper is fixed-embedding equivalent to the refuted collar-layer surface |
| `Shells.lean` | Bundled hypothesis packages (`ClosedWalkExactShell`, `SuccessorCycleExactShell`, `ClosedWalkCancellationShell`, …) replacing the historical 8–10-hypothesis telescopes |
| `Frontier.lean` | The maximal positive and negative results, stated over the bundles as thin wrappers, including detector-based cancellation sufficiency |
| `CAP5RouteVerdict.lean` | The current CAP5/F2 route verdict: either the executable report returns a concrete primitive portal/cycle checker gap, or the closed-frontier route is exactly the absence of the concrete target/off-target F2 evaders; it also names the unified emitted-kernel/remaining-map evader and proves, under no primitive gap, that this evader exists exactly when the closed route endpoint fails; in that same branch the CAP5/Jordan geometric separator repair is blocked by the cyclic-cut obstruction |
| `CAP5RoutePayoff.lean` | Route payoff extraction: a closed CAP5/F2 route certificate gives theorem-4.9 synthesis plus genuine line-graph `EdgeColorable 4` from the root `Color` edge-coloring; the missing stronger Tait upgrade is isolated as `CAP5RouteClosedRootTaitBridge`; the finite no-gap pre-RREF input is named as `CAP5FiniteNoGapRouteInput`; and the exact finite wheel route-closed canary is named as `WheelCAP5FiniteRouteClosedCanary` |

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
`enumeratedExceptionalAnnulusForcedEdgeClassifierBoundaryZeroControl_iff_no_boundaryZeroEvader`,
`enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader`
and
`theorem49BoundaryTargetClassifierControl_iff_no_targetEvader` say that the
emitted CAP5 classifier coordinates control the full selected-boundary-zero
carrier, any chosen boundary-zero Kirchhoff target, and the theorem-4.9 target
`W0(H)`, exactly when no nonzero chain in the corresponding carrier evades
every enumerated CAP5 forced edge.  This does not decide the exact shell, but
it removes the algebraic ambiguity in the oracle statement: the remaining
Move-2 fork is now to prove that exact CAP5 data supplies the no-evader side,
or to exhibit the evader.

The no-evader direction now lands on the full boundary-zero classifier-control
surface, not only the theorem-4.9 target.  Lean proves
`theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_no_missing_finsetControl`
and the executable interior-support specialization
`theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`:
a closed CAP5 checker plus absence of a nonzero selected-boundary-zero evader
yields theorem-4.9 synthesis and proves that the emitted CAP5 coordinates
control the whole selected-boundary-zero subspace.  The remaining problem is
therefore not this direction of the oracle; it is deriving the no-evader
verdict from uniform exact-shell data, or producing the genuine evader.

Update 2026-06-29: the CAP5/F2 continuation is now packaged as a route verdict
in `CAP5RouteVerdict.lean`.  The theorem `cap5F2Route_irreducibleBarrier`
assembles the oracle, the target/off-target F2 split, and the geometric
CAP5/Jordan obstruction into one top-level statement.  Under the standard
cyclic-five finite F2 route data, Lean returns either a primitive
portal/cycle checker gap, or a closed-frontier equivalence:
no target/off-target F2 evaders iff theorem-4.9 synthesis plus full
selected-boundary-zero classifier control.  In the same closed-frontier
branch, the exceptional CAP5/Jordan cyclic-separator repair is impossible.
This is an irreducible-barrier verdict on this route, not a proof of 4CT and
not a positive-canary 4-colorability sufficient condition.

Follow-up on 2026-06-29: the primitive checker frontier was sharpened inside
`CAP5RouteVerdict.lean`.  Lean now proves that
`CAP5PrimitiveCheckerGap` is exactly nonempty
`missingCheckerEvidenceLatents` in the executable 16-latent report; conversely,
emptying that report is exactly `¬ CAP5PrimitiveCheckerGap`.  The same file
also proves that no primitive gap forces portal crossings for every latent and
forces both graph-side cycle witnesses, while absence of either side-cycle
witness immediately inhabits the primitive checker gap.  This is the precise
proof-level reason the current route verdict remains a barrier rather than an
unconditional closure: exact CAP5 data still has to supply the portal/cycle
evidence and decide the target/off-target F2 evader set, or accept the concrete
gap/evader branch already returned by the formal route.

Second follow-up on 2026-06-29: the side-condition discharge was pushed through
the packaged budget oracle as far as the current definitions permit.  The
theorem `budgetMetNoEvader_boundaryZeroControl_oracle_of_noGap` derives the
oracle's broad portal-crossing premise, both side-cycle witnesses, and the
no-missing checker premise from the single hypothesis
`¬ CAP5PrimitiveCheckerGap`.  The new constructor
`CAP5F2RouteCertificate.ofNoGap` does the same for the top-level route
certificate.  Lean also proves
`not_forall_no_cap5PrimitiveCheckerGap_allSides`: a completely side-uniform
checker-gap discharge is impossible because the constant-empty side has no
selected-side cycle and therefore directly inhabits `CAP5PrimitiveCheckerGap`.
So the remaining side-condition seam is not a report/latent transport gap; it
is the need to prove that the actual CAP5 side selected by exact shell data has
the two cycle witnesses and no primitive checker gap.  The surviving algebraic
barrier is now named directly: `CAP5F2UnifiedKernelMapEvader` is the unified
emitted-kernel/remaining-map obstruction, and under no primitive checker gap
Lean proves `CAP5F2NoUnifiedKernelMapEvader` iff `CAP5F2RouteClosed`, while
existence of such an evader is equivalent to failure of that closed endpoint.

Payoff follow-up on 2026-06-29: `CAP5RoutePayoff.lean` extracts the route
payoff without re-deciding the pinned unified-evader barrier.  The theorem
`cap5RouteClosedColoringPayoff_of_routeClosed` turns `CAP5F2RouteClosed cert`
into a bundle containing theorem-4.9 synthesis and `G.EdgeColorable 4`.  The
colorability statement is real line-graph `Colorable 4`, but it comes from the
root `G.EdgeColoring Color`; route-closed alone does not state that the root
coloring is nonzero on every edge.  That stronger upgrade is now the single
named bridge `CAP5RouteClosedRootTaitBridge cert`, consumed by
`taitColorable_of_routeClosedRootTaitBridge`.  The wheel-with-inner-triangle
graph has the proven coloring canary `WheelCAP5RoutePayoff.wheelColoringCanary`.
The exact positive CAP5 canary still missing is
`WheelCAP5RoutePayoff.WheelCAP5FiniteRouteClosedCanary`: one finite checker
report plus a closed CAP5/F2 route certificate for that concrete wheel graph.
The finite pre-RREF input is now explicit too:
`CAP5FiniteNoGapRouteInput` combines a closed executable primitive-checker
report, the concrete forced-edge classifier, and all emitted/remaining
red-blue single-coordinate witnesses into the `CAP5F2RouteCertificate`
consumed by the unified-evader oracle.  So the next make-or-break test is not
another route fork; it is to instantiate that input for the actual side and
check `CAP5F2NoUnifiedKernelMapEvader`, or accept the named obstruction it
would fail on.

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

The empty-worklist path now has a structural obstruction rather than just an
implementation gap.  Lean proves
`exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport`
and
`not_remainingInteriorSupportEmpty_of_closed_walk_odd_length_in_interiorSupport`:
if an odd closed walk is entirely supported by ambient interior-support edges,
then any Boolean CAP5 forced-edge classifier leaves a concrete remaining
interior-support edge, with a strict erasure decrease of the canonical
worklist.  Therefore the all-interior empty-worklist proof path cannot be
uniform over odd-interior-walk supports.  Exact CAP5 data must either exclude
that structure while reaching the subset certificate, or the surviving branch
has to be pushed into the genuine vertex-Kirchhoff evader theorem already
formalized above.

The target-controlled executable fork now packages that pressure in one theorem
surface instead of leaving it spread across conditional lemmas.  Lean proves
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`:
with an empty checker report and target classifier control, the route returns
either theorem-4.9 synthesis plus target coverage, or a genuine
forced-edge-vanishing boundary-zero evader with nonzero Kirchhoff sum at a
theorem-4.9 boundary vertex and a decreasing remaining worklist edge.  The
odd-interior specialization
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_oddInteriorWorklistEdge_of_closed_walk_odd_length_in_interiorSupport`
adds that an odd closed walk in ambient interior support unconditionally leaves
such a remaining worklist edge.  Thus the exact shell cannot silently use the
empty-worklist subset proof on odd-interior supports; it must either prove the
target-controlled synthesis side by other exact CAP5 data or expose the
vertex-Kirchhoff evader branch.

The success side now excludes the odd-interior obstruction internally.  Lean
proves
`not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges`:
if every ambient interior-support edge is enumerated as forced by one CAP5 side,
then no odd closed walk lies in ambient interior support.  The route-facing
wrappers
`interiorSupportForced_synthesis_and_boundaryTargetCoverage_and_no_closed_odd_walk`
and
`remainingInteriorSupportEmpty_synthesis_and_targetCoverage_and_no_closed_odd_walk`
therefore say that the all-interior/empty-worklist subset branch both closes
theorem-4.9 synthesis with target coverage and certifies that the
odd-interior-worklist obstruction is absent.  The remaining exact-shell work is
not to reconcile those branches; it is to prove exact CAP5 data reaches this
success branch, or to instantiate the already formalized vertex-Kirchhoff
evader branch.

The complementary no-evader side now survives the odd-worklist witness itself.
Lean proves
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_and_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`:
if an odd closed walk lies in ambient interior support, the canonical worklist
is still nonempty, but target classifier control plus absence of the concrete
theorem-4.9 boundary-vertex Kirchhoff evader closes synthesis and target
coverage anyway.  Thus the odd-worklist obstruction only blocks the
empty-worklist proof path; it is not itself the surviving algebraic failure
mode.  The exact shell must now supply the no-evader/subset certificate by
other CAP5 data or produce the genuine vertex-Kirchhoff evader.

The executable CAP5 report now feeds directly into that algebraic fork.  Lean
proves
`theorem49Synthesis_and_boundaryZeroControl_of_noEvader_of_forcedAllLatents`,
`remainingInteriorEmpty_synthesis_and_targetCoverage_of_forcedAllLatents`, and
`targetControlledSynthesis_or_evader_of_forcedAllLatents`: under cyclic
five-edge-connectivity, the report verdict
`forcedCounterexampleLatents = all` closes the primitive missing-evidence
frontier and drives the existing F2 endpoints.  With a no-evader verdict it
yields theorem-4.9 synthesis plus full boundary-zero classifier control; with
an empty canonical interior-support worklist it yields the subset-certificate
success side; under target classifier control it returns the exact
synthesis-versus-genuine-vertex-Kirchhoff-evader fork.  This still does not
prove that exact CAP5 shell data supplies the no-evader/subset certificate,
but it removes the raw `missingCheckerEvidenceLatents = []` premise from the
route-facing F2 checkpoint.

The report-forced-all target-controlled interface is now split into its two
actual fork halves.  Lean proves
`targetControlledSynthesis_of_noEvader_of_forcedAllLatents` and
`targetControlledEvader_of_notSynthesis_of_forcedAllLatents`: once
`forcedCounterexampleLatents = all` closes the primitive missing-evidence
frontier, target classifier control plus absence of the concrete theorem-4.9
boundary-vertex Kirchhoff evader yields synthesis and target coverage; if
synthesis still fails, Lean returns exactly that genuine evader together with
a decreasing remaining-worklist edge.  This removes an interface ambiguity in
the executable report path, but it does not by itself prove that exact
CAP5/Jordan shell data supplies the no-evader/subset side.

The same report-forced-all failure branch now has a canonical path-xor payload
form.  Lean proves
`canonicalPayloadEvader_of_notSynthesis_of_forcedAllLatents` and
`synthesis_or_canonicalPayloadEvader_of_forcedAllLatents`: if the forced-all
report branch still fails theorem-4.9 synthesis, the canonical interior-support
runner returns the finite artifact the lab is designed to expose, namely a
forced-bin path-xor detector payload, a selected-boundary-zero chain vanishing
on every enumerated forced edge, a concrete remaining interior edge that is
not forced and where the chain is nonzero, a strict worklist decrease, and a
nonzero canonical red/blue family pairing.  This does not prove the exact-shell
no-evader/subset side, but it makes the alternative branch computational rather
than only existential.

The forced-all branch now also exposes the pure no-target F2 evader fork.  Lean
proves
`boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_notSynthesis_of_forcedAllLatents`
and
`theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`:
once the report forces all latents, failed theorem-4.9 synthesis is already a
genuine selected-boundary-zero evader for the enumerated CAP5 forced edges,
together with a decreasing remaining interior-support worklist edge.  The
target-controlled and canonical path-xor payload branches are therefore
refinements of this basic evader branch, not separate failure modes.

The forced-all F2 oracle is now packaged as the route-facing decision itself.
Lean proves
`theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroEvader_of_forcedAllLatents`:
once the report forces all latents, either the no-evader verdict closes
theorem-4.9 synthesis plus full selected-boundary-zero classifier control, or
there is an actual nonzero selected-boundary-zero evader for the enumerated
forced edges.  This is the correct fork surface for the remaining lab-to-Lean
work: exact CAP5/Jordan shell data must now supply the no-evader/subset side,
or the explicit evader side is the obstruction to formalize.

The empty-worklist side of that fork now carries the actual no-evader verdict.
Lean proves
`remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents`:
if the forced-all report has no remaining canonical interior-support worklist,
then every interior-support coordinate is already emitted as a forced edge, no
nonzero selected-boundary-zero chain can vanish on all forced edges, and
theorem-4.9 synthesis follows with full selected-boundary-zero classifier
control.  Thus the remaining exact-shell task is not to reinterpret the
empty-worklist certificate; it is to prove uniform CAP5/Jordan data reaches it
or to formalize the evader/worklist branch.

The forced-all finite scheduler fork is now explicit as well.  Lean proves
`remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_or_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`:
after the executable report has forced all latents, either the empty-worklist
no-evader/full-control branch holds, or there is a concrete remaining
interior-support edge whose erasure strictly decreases the finite worklist.
This makes the next exact-shell obligation operational: prove the remaining
worklist is empty from uniform CAP5/Jordan data, or use the returned edge to
drive the finite scheduler toward an evader/worklist obstruction.

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
with the shell-wide one-collar obstruction.  The repair-removal side is now
exposed at the graph-facing cyclic-cut interface as well:
`CAP5ExceptionalCyclicSeparatorRepairRealization`,
`not_CAP5ExceptionalCyclicSeparatorRepairRealization_of_cyclicallyFiveEdgeConnected`,
and
`closedWalkExactShell_oneCollar_and_CAP5CyclicSeparatorRepair_obstruction`
say that realizing even one compatible exceptional CAP5/Jordan candidate as
cyclic-cut data produces a cyclic edge cut of size at most four, impossible in
a cyclically five-edge-connected graph; the wrapper packages this with the
exact-shell one-collar/canonical obstruction.  The remaining geometric work is
to close the residual generator surface.

The residual generator surface is now classified and decision-shaped.  In
`FrontierGeometric.lean`,
`closedWalkExactShell_oneCollar_and_CAP5GeneratorNode_residualClassifier`
proves that a generated CAP5 separator node in a cyclically five-edge-connected
graph is either missing primitive checker evidence or emits the concrete
outside-crossing edge outside candidate support.  The report-level theorem
`closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_residualClassifier`
adds the finite 16-latent statement: every generated latent is forced exactly
when the missing-evidence frontier is empty, and if not, Lean returns a
specific missing-evidence latent.  The new report-decision theorem
`closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_geometricRepairDecision`
uses the report equivalences
`missingCheckerEvidenceLatents_eq_nil_iff_all_checker_evidence` and
`missingCheckerEvidenceLatents_ne_nil_iff_exists_failed_checker_evidence`:
the missing branch is exactly failure of the primitive portal/cycle
prerequisites for the realized CAP5/Jordan separator-repair class; if those
prerequisites are present, the report is forced-all and the completed
repair branch is blocked by the same cyclic-five small-cut obstruction.
The completed-prerequisite wrapper
`closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction` records that
closed branch without another report fork: once the missing-evidence frontier
is empty, cyclic five-edge-connectivity forces all generated latents into the
counterexample bin and forbids the exceptional cyclic-separator repair
realization by the size-at-most-four cyclic-cut obstruction, while the
closed-walk shell still blocks the canonical and one-collar repair surfaces.
Thus the residual Move-1 task is no longer another packet refutation: either
prove exact shell data supplies the primitive prerequisites, or keep failed
prerequisites as outside the realized repair class.

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
   normal form.  The repair-removal surface now also has the fundamental
   small-cut obstruction: any compatible exceptional CAP5/Jordan candidate
   realized as cyclic-cut data is a forbidden cyclic edge cut of size at most
   four under cyclic five-edge-connectivity.  The residual generator/report
   layer is now decision-shaped: under cyclic five-edge-connectivity every
   generated node either emits the outside-crossing edge outside candidate
   support or is missing primitive checker evidence; report-level missing
   evidence is exactly failure of the primitive portal/cycle prerequisites for
   the realized separator-repair class; and if those prerequisites are present,
   the completed branch is forced-all and blocked by the small-cut
   obstruction.  The completed-prerequisite wrapper
   `closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction` names that
   branch as the single CAP5/Jordan small-cut obstruction.  The remaining
   Move-1 gap is to prove exact shell data supplies those primitive
   prerequisites, or keep failed prerequisites outside the realized CAP5/Jordan
   repair class.
2. **Algebraic fork**: resolve the F2 cancellation oracle.  The current
   machine-checked statement is now packaged rather than exposed as case
   cartography: with the primitive checker gap absent,
   `budgetMetNoEvader_boundaryZeroControl_oracle` proves no unified
   emitted-kernel/remaining-map evader iff theorem-4.9 synthesis plus full
   selected-boundary-zero classifier control, and failure returns that same
   precise unified evader.  The supporting statements remain sharper than a
   one-way handoff: full
   selected-boundary-zero classifier control is equivalent to absence of a
   nonzero selected-boundary-zero evader, and the closed finite checker plus
   that no-evader verdict gives both theorem-4.9 synthesis and full
   boundary-zero classifier control.  The emitted-edge red/blue pairing kernel
   is now exact for the same no-evader verdict, so a finite rank certificate on
   the immutable emitted forced-edge coordinates closes the forced-all route,
   while kernel failure returns a genuine selected-boundary-zero evader;
   classifier control of the theorem-4.9
   target is also equivalent to absence of a nonzero target evader;
   underdimensioned classifiers produce a genuine target evader; target
   classifier control reduces the remaining failure branch to a
   forced-edge-vanishing selected-boundary-zero evader with a concrete
   theorem-4.9 boundary-vertex Kirchhoff failure, plus a decreasing worklist
   edge; and the row-span/subset bridge says the exact remaining certificate is
   that every forced-vanishing boundary-zero chain lies in the theorem-4.9
   target.  The empty-worklist shell
   now proves that exact subset certificate and eliminates the concrete
   vertex-Kirchhoff evader branch there, while odd-interior supports refute
   that empty-worklist proof path.  The all-interior/empty-worklist success
   side now also certifies that no odd interior closed walk exists, so the
   subset/no-evader branch explicitly excludes the odd-worklist obstruction;
   conversely, the new odd-interior no-evader closure shows that a nonempty
   odd-worklist witness does not prevent synthesis once the concrete
   vertex-Kirchhoff evader is excluded.  The target-controlled executable
   theorem packages the uniform route as synthesis/target coverage or a
   genuine vertex-Kirchhoff evader plus a decreasing worklist edge.  The
   generator report bridge now lets the route consume
   `forcedCounterexampleLatents = all` directly in place of the raw empty
   missing-evidence premise, and feeds that report verdict into full
   boundary-zero no-evader control, empty-worklist subset success, or the
   target-controlled synthesis-or-evader fork.  That report-forced-all fork is
   now split into its no-evader and failed-synthesis halves: absence of the
   concrete vertex-Kirchhoff evader closes synthesis, while failed synthesis
   produces the evader and a decreasing remaining-worklist edge.  The same
   forced-all failure side now also exposes the canonical path-xor payload
   evader: a boundary-zero chain, non-forced remaining interior edge, strict
   worklist decrease, and nonzero canonical red/blue family pairing.  The new
   residual scheduler wrapper records the same failure inside an explicit
   processed-state trace: complete checker histogram, forced-bin detector,
   selected-boundary-zero evader, traced remaining interior-support edge,
   residual-worklist membership, and strict residual decrease after inserting
   that edge into the processed set.  The residual transition theorem then
   proves the selected edge is not controlled by the immutable classifier
   output and returns the one-edge emitted/control update needed to insert it
   into the processed scheduler state.  The terminal residual-scheduler theorem
   closes the matching success endpoint: residual exhaustion plus the
   processed-control invariant proves no selected-boundary-zero evader, theorem
   4.9 synthesis, and full selected-boundary-zero classifier control.  The
   failed-terminal scheduler theorem now connects those endpoints: failed
   synthesis under forced-all cannot be sitting at an exhausted residual
   worklist, and instead returns a selected-boundary-zero evader, the next
   residual edge, immutable-control failure for that edge, the one-edge
   emitted/control update, and strict residual decrease.  The
   immutable-scheduler obstruction theorem then rules out the tempting but
   invalid next move: that same edge cannot be marked processed under the
   original classifier output.  Continuing the scheduler requires adding the
   one-edge emitted/control update as real new control information, or keeping
   the evading boundary-zero chain as the obstruction.  The route-facing
   residual scheduler decision now packages the current finite state into the
   exact alternatives needed by Move 2: terminal no-evader/synthesis,
   already-closed synthesis, or a promoted one-edge obstruction with immutable
   processing ruled out and strict residual decrease.  The coverage-form
   scheduler theorem then restates the terminal branch as the semantic
   invariant that the processed set covers every original remaining control
   edge, while preserving the same already-closed synthesis branch and promoted
   obstruction branch.  The trace-control fork now makes this terminal
   algebraic surface exact: canonical remaining-interior trace-control is
   equivalent to absence of a selected-boundary-zero evader, and failure of
   trace-control returns a genuine evader plus a concrete trace edge where it
   is nonzero.  The failure side now also carries the canonical red/blue
   single-coordinate family obstruction: with the remaining-edge generator
   certificates, the same trace-local evader has a nonzero canonical family
   pairing on that edge.  The remaining-family map oracle now makes the finite
   F₂ detector surface explicit: every genuine selected-boundary-zero evader
   has nonzero image under the canonical remaining-edge family-pairing map,
   while emitted classifier zeros plus zero image under that map force the
   boundary-zero chain itself to be zero.  The exact split now proves that
   absence of a map-detected evader is equivalent to absence of a
   selected-boundary-zero evader.  Under the forced-all report, trace-control,
   or equivalently no map-detected evader, closes theorem-4.9 synthesis plus
   full selected-boundary-zero classifier control; otherwise Lean returns the
   map-detected evader as the obstruction.  The emitted-edge kernel bridge now
   connects the lab-facing rank certificate directly to that same oracle: the
   canonical red/blue pairing kernel on the immutable emitted forced-edge
   coordinates is trivial iff no selected-boundary-zero evader exists.  Under
   forced-all this emitted-kernel certificate closes synthesis/control; failure
   returns a concrete nonzero selected-boundary-zero kernel witness vanishing
   on every enumerated forced edge.  The emitted-kernel/map equivalence now
   collapses the two failure languages: a nontrivial emitted-kernel witness has
   nonzero remaining-family map image, and a map-detected evader lies in the
   emitted kernel.  The forced-all rank fork therefore returns either
   synthesis/control or one genuine boundary-zero evader carrying both the
   emitted-kernel and remaining-map certificates.  The failed-synthesis
   corollary removes the success side from that fork under
   `¬ Theorem49BoundaryRootSynthesis`: if synthesis fails, Lean directly
   returns the unified emitted-kernel/remaining-map evader.  The exact
   kernel/map oracle theorem now gives the corresponding iff: under forced-all,
   no unified emitted-kernel/remaining-map evader is equivalent to theorem-4.9
   synthesis plus full selected-boundary-zero classifier control.  The exact
   emitted-rank oracle then makes the lab-facing finite F2 certificate itself
   equivalent to route closure: under forced-all, the emitted-edge pairing
   kernel is trivial iff theorem-4.9 synthesis plus full selected-boundary-zero
   classifier control holds.  The report-closed emitted-rank wrapper now removes
   that raw handoff from the public route state: the executable CAP5 report
   either has a primitive portal/cycle checker gap, or its closed frontier
   supplies forced-all and the same emitted-rank iff applies.  The stronger
   report-closed trace wrapper now removes the same raw handoff from the
   canonical trace-control fork: the executable report returns a primitive
   checker gap, theorem-4.9 synthesis with full selected-boundary-zero control,
   or a genuine trace-local selected-boundary-zero evader with a concrete
   remaining trace edge and nonzero canonical remaining-family pairing.  The
   failure-only report trace theorem removes the success branch under
   `¬ Theorem49BoundaryRootSynthesis`, so a failed route now returns a
   primitive checker gap or that trace-local evader directly.  The
   failure-only report kernel/map theorem gives the same failed route in the
   lab-facing rank language: primitive checker gap or unified
   emitted-kernel/remaining-map evader.  The report-level kernel/map split and
   no-gap/no-evader closure corollary give the complementary positive
   direction: excluding both primitive checker gaps and the unified
   emitted-kernel/remaining-map evader closes theorem-4.9 synthesis plus full
   selected-boundary-zero classifier control.  The exact report-level
   kernel/map oracle strengthens this to an iff: after a closed primitive
   frontier, no unified evader is equivalent to synthesis/control, and the
   executable report returns either a primitive gap or that exact equivalence.
   The emitted-rank/no-unified-evader bridge now identifies the lab-facing
   finite kernel certificate with absence of that unified obstruction after the
   same closed primitive frontier.  The report-level emitted-rank trichotomy
   then packages the finite verdict as the actual executable branch:
   primitive checker gap, emitted-rank close with synthesis/control, or
   rank-failure unified evader.  The target/off-target oracle is now tied to
   that same rank certificate:
   `no_boundaryZeroEvader_iff_theorem49BoundaryTargetClassifierControl_and_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   decomposes full no-evader into theorem-4.9 target classifier control plus
   absence of the concrete off-target boundary-vertex Kirchhoff evader, and
   `emittedFinsetPairingKernel_eq_bot_iff_theorem49BoundaryTargetClassifierControl_and_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   proves the emitted-edge pairing kernel is trivial exactly when this
   decomposed target/off-target oracle is closed.  The failure side is now
   route-facing as well:
   `emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_emittedFinsetPairingKernel_eq_bot_of_theorem49BoundaryTargetClassifierControl`
   proves that once target classifier control is known, emitted-rank failure
   returns the genuine evader with emitted-kernel membership, nonzero
   remaining-map image, and a concrete theorem-4.9 boundary-vertex Kirchhoff
   failure.
   The target-controlled split is now also an exact local rank decision:
   `emittedFinsetPairingKernel_eq_bot_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl`
   proves that, after theorem-4.9 target control, emitted-rank triviality is
   equivalent to absence of that concrete off-target Kirchhoff evader, and
   `emittedFinsetPairingKernel_eq_bot_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl`
   packages the close-or-witness branch with emitted-kernel and nonzero
   canonical remaining-map certificates.  The target-control side condition is
   now removed from the failure interpretation:
   `theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_emittedFinsetPairingKernel_eq_bot`
   turns nontrivial emitted-rank failure into either a nonzero theorem-4.9
   target chain vanishing on every enumerated forced edge or the off-target
   kernel/map/vertex-failure evader, and
   `emittedFinsetPairingKernel_eq_bot_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   packages the local finite F2 verdict as close, target evader, or off-target
   evader.  The same target/off-target split is now report-level:
   `ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   packages the executable branch as primitive checker gap, emitted-rank close
   with synthesis/control, target evader, or off-target kernel/map/vertex
   evader, and
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_theorem49BoundaryRootSynthesis`
   removes the close branch under failed synthesis.  A closed-frontier
   corollary now states the no-evader side in exactly this
   target/off-target vocabulary:
   `emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_iff_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missingCheckerEvidence`
   proves that, once the primitive checker frontier is closed, emitted-rank
   close with synthesis/control is equivalent to absence of both target-side
   and off-target report evaders.  The rank-certificate corollary
   `emittedFinsetPairingKernel_eq_bot_iff_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missingCheckerEvidence`
   removes the bundled-success wording: under the same closed primitive
   frontier, the emitted F2 pairing-kernel certificate itself is equivalent to
   absence of both concrete report evaders, with synthesis/control recovered
   from that certificate.  The emitted-rank route-close corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_emittedFinsetPairingKernel_eq_bot`
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_emittedFinsetPairingKernel_eq_bot`
   now consume that finite rank certificate directly: the executable report
   has only primitive checker gap or synthesis/control left, and with the
   primitive frontier closed the certificate directly proves synthesis/control.
   The coverage-to-rank bridge
   `emittedFinsetPairingKernel_eq_bot_of_forcedEdgeCoverage`,
   `emittedFinsetPairingKernel_eq_bot_of_controlEdges_nonzeroCoverage_subset_emittedFinset`,
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_forcedEdgeCoverage`,
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_forcedEdgeCoverage`
   now connect the lab no-evader/coverage verdict to that rank certificate:
   exact forced-edge coverage, or a finite control set that meets every
   nonzero selected-boundary-zero chain and is already emitted by the
   classifier, proves the emitted red/blue pairing-kernel certificate consumed
   by the executable report route.
   The exact-shell empty-worklist specialization
   `emittedFinsetPairingKernel_eq_bot_of_remainingInteriorSupportEmpty`,
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_remainingInteriorSupportEmpty`,
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_remainingInteriorSupportEmpty`
   now proves the same emitted-rank certificate directly from the concrete
   CAP5 condition that the canonical interior-support worklist is empty.
   The report-level exact-worklist fork
   `remainingInteriorSupportEmpty_closes_or_notSynthesis_boundaryZeroEvader_and_nonempty_worklist_of_no_missingCheckerEvidence`
   makes the remaining Move-2 decision boundary explicit: with the primitive
   checker frontier closed, empty worklist closes synthesis/control, while
   failed synthesis forces a nonempty worklist and returns a genuine
   selected-boundary-zero evader plus a decreasing remaining-worklist edge.
   The executable-report exact-worklist fork
   `ofDecidableChecks_missingCheckerEvidence_or_remainingInteriorSupportEmpty_closes_or_notSynthesis_boundaryZeroEvader_and_nonempty_worklist`
   removes the raw closed-frontier handoff from that statement: the report now
   returns either a primitive checker gap or the same exact worklist fork.
   The executable-report residual scheduler fork
   `ofDecidableChecks_missingCheckerEvidence_or_residualSchedulerCoverageNoEvader_or_synthesis_or_immutableProcessedControlObstruction_of_processedControl`
   and its failure-only corollary
   `ofDecidableChecks_missingCheckerEvidence_or_residualSchedulerImmutableProcessedControlObstruction_of_notSynthesis_of_processedControl`
   now remove the raw forced-all handoff from the promoted scheduler as well:
   the report returns either a primitive checker gap or the terminal
   processed-coverage no-evader/synthesis branch, an already-closed synthesis
   branch, or a promoted residual-edge obstruction; under failed synthesis,
   only the primitive gap or the genuine residual selected-boundary-zero
   evader with immutable processed-control failure and strict residual decrease
   remains.
   The initial residual scheduler corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_initialResidualSchedulerNoEvader_or_synthesis_or_immutableProcessedControlObstruction`
   and
   `ofDecidableChecks_missingCheckerEvidence_or_initialResidualSchedulerImmutableProcessedControlObstruction_of_notSynthesis`
   remove the scheduler-side processed-state handoff altogether at the start:
   `processed = ∅` supplies processed-control automatically, so the executable
   report itself starts the promoted scheduler.  Failed synthesis now returns
   either the primitive gap or the first residual selected-boundary-zero evader
   with immutable one-edge processed-control failure, the one-edge promoted
   control update, and strict residual decrease.
   The initial residual closure layer
   `InitialResidualSchedulerImmutableProcessedControlObstruction`,
   `emittedFinsetKernelMapEvader_of_initialResidualSchedulerImmutableProcessedControlObstruction`,
   `initialResidualSchedulerImmutableProcessedControlObstruction_of_no_missingCheckerEvidence_of_notSynthesis`,
   `emittedFinsetKernelMapEvader_of_no_missingCheckerEvidence_of_notSynthesis_via_initialResidualScheduler`,
   `theorem49BoundaryRootSynthesis_of_no_missingCheckerEvidence_and_no_initialResidualSchedulerImmutableProcessedControlObstruction`,
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_initialResidualRemainingControlEdgesEmpty`,
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_initialResidualRemainingControlEdgesEmpty`
   turns that fork into a direct route decision: no primitive checker gap plus
   an initially empty residual scheduler proves theorem-4.9 synthesis with full
   selected-boundary-zero classifier control, while no primitive checker gap
   plus failed synthesis forces the named first residual evader/immutable
   processing obstruction.  That obstruction now promotes to the same unified
   emitted-kernel/remaining-map evader used by the finite F2 rank oracle, so
   the nonempty initial scheduler branch is no longer a separate branch from
   the emitted-rank/map fork.  The remaining Move-2 burden is therefore to
   prove exact CAP5 shell data empties that initial residual scheduler/emitted-
   rank certificate, or to accept the named first residual obstruction as the
   unified finite F2 evader.
   The focus-shell threshold bridge
   `sharedInteriorPair_CAP5_initialResidualRemainingControlEdges_eq_empty_iff_emittedInterior_card_ge_two`
   and
   `wheelWithInnerTriangle_CAP5_initialResidualRemainingControlEdges_eq_empty_iff_emittedInterior_card_ge_three`
   resolves that question for the two current lab focus shells: the shared
   interior-pair shell has an empty initial residual worklist exactly when both
   shared controls are emitted, and the inner-triangle wheel shell has an empty
   initial residual worklist exactly when all three spoke controls are emitted.
   The paired synthesis and contrapositive corollaries close the
   boundary-trimmed unique-certificate route from those empty worklists, while
   failed synthesis forces a genuinely nonempty initial residual worklist.  The
   remaining question is now the uniform exact CAP5 shell-data lift of these
   finite focus thresholds, not another isolated repair-packet refutation.
   The uniform scheduler bridge
   `initialResidualRemainingControlEdges_eq_empty_iff_controlEdges_subset_emittedFinset`
   now identifies the initial residual condition for any finite control set
   with the concrete fixed point that all chosen controls are already emitted.
   The report-facing corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_initialResidualInteriorSupport_subset_emittedFinset`
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_initialResidualInteriorSupport_subset_emittedFinset`
   therefore state the exact remaining shell-data handoff directly: if the
   canonical `interiorEdgeSupport` is contained in the emitted classifier
   output, then the remaining-edge certificate obligations are vacuous, the
   initial residual scheduler is empty, and the report route closes to
   synthesis/full selected-boundary-zero control except for primitive checker
   gaps.  The Move-2 lift target is now this emitted-interior-support subset,
   uniformly.
   The failure-side corollaries
   `exists_initialResidualInteriorSupportEdge_not_emitted_of_no_missingCheckerEvidence_of_notSynthesis`
   and
   `initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader_of_no_missingCheckerEvidence_of_notSynthesis`
   make the opposite side equally concrete: with the primitive checker frontier
   closed, failed theorem-4.9 synthesis forces a residual canonical
   interior-support edge outside the emitted classifier output, and returns it
   together with the unified emitted-kernel/remaining-map F2 evader.  So the
   exact shell-data handoff is now a true close-or-witness fork: prove emitted
   canonical interior-support subset, or accept the missing interior coordinate
   plus the unified finite F2 obstruction.
   The report-level wrappers
   `ofDecidableChecks_missingCheckerEvidence_or_initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader_of_notSynthesis`
   and
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_or_initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader`
   remove the remaining closed-frontier handoff from this paired obstruction:
   the executable report itself now returns primitive checker gap, synthesis,
   or the paired missing-interior-coordinate plus unified finite F2 evader.
   The packaged theorem
   `budgetMetNoEvader_boundaryZeroControl_oracle` is the assembled oracle
   surface over those case lemmas: with the primitive checker gap absent, no
   unified emitted-kernel/remaining-map evader is equivalent to theorem-4.9
   synthesis plus full selected-boundary-zero classifier control; if that
   closed result fails, the theorem returns the same precise unified evader.
   The remaining exact-shell question is therefore the no-evader certificate
   itself, not another scheduler/rank/report split.
   The direct no-evader route corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   now expose the decision step in the requested form: excluding both concrete
   evader branches leaves only primitive checker gap or synthesis/control, and
   with the primitive frontier closed it directly proves synthesis/control.
   The higher edge-cap/coloring-cap
   projected-generator lab run now records this distinction explicitly: among
   65 reports there are 53 found coordinate-probe reports, 12 no-Tait-coloring
   reports, and 0 missing probe reports.
   These projected probes are supporting realization evidence, not the
   emitted-kernel rank certificate needed by the Lean oracle.  The
   pure no-target theorem underneath those refinements says failed synthesis
   already produces a genuine selected-boundary-zero evader for the enumerated
   forced edges.  The remaining crux is whether exact shell/CAP5 data reaches
   canonical remaining-interior trace-control/emitted-kernel triviality
   uniformly, or whether this
   genuine boundary-zero/vertex-Kirchhoff/path-xor trace-local evader with
   canonical red/blue pairing/map/kernel signal is the decided obstruction.

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
