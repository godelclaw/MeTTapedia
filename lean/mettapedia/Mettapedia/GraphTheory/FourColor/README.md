# FourColor

This is the canonical modern Lean home for the godelclaw Four Color work.

## Current proof plan — 30 September 2026

Start with the [compositional proof-plan guide](../../../../../papers/benxiv/fourcolor-compositional/README.md).
It connects Goertzel and Fable's original three-level argument to the current
Lean results and identifies where the completed repair changes the proof.

The [classical integration package](../../../../fourcolor-classical/README.md)
now proves four-colourability for finite simple graphs with noncrossing plane
drawings and supplies compatible GSLT colouring witnesses for exact
constructions of every bridgeless spherical cubic source map. The checked
root is [MettapediaFourColor.Complete](../../../../fourcolor-classical/MettapediaFourColor/Complete.lean).
All 633 catalogue entries remain. The complete proof retains 630 reference
configuration certificate dependencies. A shared finite joint-profile repair
supplies configurations 2 and 4, and a general boundary-split law transfers
repair from configuration 2 to configuration 1. Shared proofs also replace
231 independent discharging computations.

This completes the classical reconstruction. The diamond cores now share
boundary laws for all their local cover obligations, retaining finite profile
and classification data. The new
[cyclic seam reduction](HexagonalTubeTwistReduction.lean) deletes two rows
from any recognized hexagonal tube of at least three rows at width `k ≥ 2`.
Rotating the attachment at one end by one port preserves the map class
and reconstructs every smaller colouring, fixing all exterior edge colours.
The total decrease is exactly `4k` vertices. No finite colouring certificate
is used. [GSLT route reconstruction](ZigzagTubeTwistGSLT.lean) composes this
directed witness map in arbitrary contexts. In the all-five/six face class,
a supplied row in a minimal counterexample now reaches a pentagonal seam
within one successful extension at width two. The constructed two-row
reduction below improves this to zero extensions at every width at least three.
The [padded-cap family](PaddedCycleCapEven.lean) now has a strict reduction
for every even `m ≥ 2`: replace its `8m` vertices by a `2m`-cycle and
reconstruct every smaller colouring while fixing the exterior. One cyclic
choice law handles all widths; evenness also closes constant boundary words.
The [geometric replacement](PaddedCycleCapReplacement.lean) preserves the
spherical cubic connected bridgeless class at every `m ≥ 2`, including odd
widths. [Exact representation transport](PaddedCycleCapTransport.lean) excludes
recognized even caps from a vertex-minimal counterexample. GSLT horizontal
composition preserves shared words and actual witnesses. The entire map
loses exactly `6m` vertices. Odd widths still require the nonconstant guard
in a fixed arbitrary exterior. The [coupled physical repair](PaddedCycleCapPhysicalGeometry.lean)
now covers every `m ≥ 2` for exactly recognized spherical shores with connected
exterior: switch an adjacent exterior component and repair the smaller cycle
together, then reconstruct the cap. The new
[face-trace recognition](PaddedCycleCapRecognition.lean) constructs that exact
representation from a central `m`-face, two hexagons and one pentagon per
sector, short outward seam faces, and an injective vertex trace. A
[uniform short-face law](Compositional/ShortFacePortExclusion.lean) derives
boundary exposure; no induced-patch check is supplied. The
[short-face connectivity law](Compositional/ShortFaceBoundaryConnectivity.lean)
joins consecutive outside endpoints by one or two actual edges. Complete
boundary classification and ambient connectivity then connect the whole
exterior. Its [cap consumer](PaddedCycleCapExteriorConnectivity.lean) removes
the separate exterior-connectivity hypothesis from the all-width strict
reduction and counts the whole-map loss exactly. The
[pentagonal separation theorem](PentagonalPaddedCapSeparation.lean) now derives
forty distinct traced vertices from the actual face closures and ambient girth.
Its compact joint routes preserve both darts and their relative slot choices;
the decoded diagram is checked against the face-trace operations. The
[face-pattern reduction](PentagonalPaddedCapReduction.lean) derives girth from
normal form, replaces the forty-vertex cap by a ten-cycle and reconstructs
every smaller colouring. No local isomorphism, vertex injection or exterior
connectivity is supplied. The shared all-width colouring law is reused;
the finite certificate checks geometry. Separation at other widths and
global occurrence coverage remain open obligations.
The [two-row wiring law](ZigzagTwoRowWiring.lean) now proves the colouring
component of a shorter stopping-case operation: at every width `k ≥ 3`,
two rows accept any nonzero word and its cyclic shift. Actual closed
reconstruction retains every exterior dart colour. The
[residual replay](../../../../../tools/fourcolor/classical/residual-coverage-probe.json)
finds a 240-vertex fullerene outside the current diamond, cap and three-row
tube patterns, and independently checks a 240→168 shifted free-wire
replacement with complete colouring reconstruction. The
[audit](ZigzagTwoRowWiringAudit.lean) checks the uniform colouring component.
The [free-wire geometry](ZigzagTwoRowWiringGeometry.lean) and
[face calculation](ZigzagTwoRowWiringFaces.lean) now prove a strict reduction
at every width `k ≥ 3`, provided the exterior has two internally connected
shores and the opposite boundary first return. Exactly `4k` vertices vanish,
with no auxiliary wire vertices. Connectedness, bridgelessness, cubic
rotation and spherical Euler characteristic are preserved. The
[embedded-slab adapter](HexagonalTwoRowWiringReduction.lean) transports the
reduction and exterior colour retention to an actual ambient map and gives
a minimal-counterexample exclusion. Its [dependency audit](ZigzagTwoRowWiringGeometryAudit.lean)
checks eleven roots independently of complete Four Colour endpoints and
finite tube stabilization. The [short-face recognition theorem](HexagonalTwoRowWiringRecognition.lean)
now derives both exterior conditions from the actual slab and five- or
six-dart ambient end faces. Its [audit](HexagonalTwoRowWiringRecognitionAudit.lean)
checks eight roots, including the strict reduction and minimality consumers.
No shore-connectivity or return-order premise is supplied to this theorem.
The [constructed-growth consumer](HexagonalTwoRowGrowthReduction.lean)
now starts from one recognized row with a hexagonal seam. Its actual collar
supplies the second row; the successor input order equals the original
output order, so assembly has the literal identity matching. The reduction
then follows without a supplied two-row occurrence or exterior conditions.
Exactly `4k` vertices disappear and every smaller colouring reconstructs
while retaining all exterior dart colours. In a minimal counterexample in
the all-five/six-face class, every recognized row of width `k ≥ 3` already
has a pentagonal seam, and recognized chains have length at most one.
The raw [alternating-cycle consumer](AlternatingCycleRecognition.lean)
locates it at an original outgoing cycle port. Its
[audit](HexagonalTwoRowGrowthReductionAudit.lean) checks ten roots without
complete classical endpoints or finite tube stabilization. Initial cycle
supply, closing lobes and pentagonal-stop reductions remain open. The
[domain replay](../../../../../tools/fourcolor/classical/two-row-free-wire-domain.json)
independently verifies those conditions in the saved 240→168 example.
Independent replay includes an all-five/six 96→60 example and the earlier
guarded GP(2,0) 80→50 example. No further catalogue dependency is removed.
See the [worked cap explanation](../../../../../papers/benxiv/fourcolor-compositional/tube-example/README.md#a-joint-colouring-law-for-padded-cycle-caps).

A simple cycle with alternating local turns now constructs that
row's facial sides and complete ordered interfaces at every width at least two;
see [AlternatingCycleRecognition](AlternatingCycleRecognition.lean).
The [enlarged supply replay](../../../../../tools/fourcolor/classical/family-supply-probe.json)
tests the diamond, recognized padded-cap and hexagonal-seam simple-cycle
union on 44 explicit maps. Thirty-nine have a qualifying occurrence; five
dual-and-truncate maps of orders 222–240 do not. Four have no simple
complete alternating orbit. The fifth has six simple width-eighteen rows,
each already meeting a pentagon. All five have explicit Tait colourings
and no nontrivial cyclic cut detected among all simple dual circuits of
length at most five. Their shortest extracted lobes have lengths 31, 33
or 35 and separate five pentagons from seven. These are independent finite
diagnostics, not kernel certificates of normal form or minimality. They
exclude unconditional coverage by the present union on these maps;
closing-lobe and pentagonal-stop laws remain necessary candidates.
There is now a [uniform dual-and-truncate colouring law](DualTruncateColoring.lean)
for another structural branch. Expanded vertices are source darts, and a
proper source three-vertex colouring gives a genuine target Tait edge
colouring by the local rule `a+b, b, a`. The
[GSLT consumer](DualTruncateConstructionGSLT.lean) supplies compatible
witnesses on every complete sweep, including exact representation adapters.
The source colouring remains an explicit input. An
[independent replay](../../../../../tools/fourcolor/classical/dual-truncate-colouring.json)
checks the source witnesses and exact dart/rotation adapters on all five
residuals: 1,152 target vertices and 3,456 darts. Those finite inputs are
not kernel certificates. Source-colouring existence and geometric family
recognition remain separate; no coverage configuration is removed.
Every alternating trajectory now supplies a [simple cycle segment](AlternatingWalkLobes.lean)
with exact facial separation and connected shores. Its internal steps stay
alternating; the closing transition is unrestricted. An independently checked
30-vertex fullerene has no simple complete alternating orbit, so that closing
transition needs its own contract. Reductions for these segments and for
pentagonal stops, width control and a broader core-family reduction remain
open. [CycleSeamTransfer](CycleSeamTransfer.lean) now proves the exact colouring
law for contracting two adjacent ports of a literal cycle, at every length:
the retained seam colour must differ from the first old port colour. It
reconstructs actual witnesses and proves that forgetting this guard fails
already on a four-cycle. The embedded exterior operation remains separate.
The larger pentagon-plus-eleven-lobe patch now admits a twelve-vertex tree
reduction and genuine colouring reconstruction for every exact recognized
occurrence under the documented spherical and exterior hypotheses. In a minimal counterexample,
[SixPortBoundaryConnectivity](SixPortBoundaryConnectivity.lean) and
[SphericalVertexLowerBound](SphericalVertexLowerBound.lean) supply exterior
connectedness without distinct attachment vertices; the
[actual consumer](../../../../fourcolor-classical/MettapediaFourColor/PentagonalLobeMinimalExterior.lean)
excludes the recognized occurrence. Recognition from the stated two-cycle
geometry is now constructed below; broader supply and coverage remain open.
The GSLT, graph and MeTTa results have their own verified consumers, listed
in the guide.

[CubicCycleIncidence](CubicCycleIncidence.lean) now derives a cycle shore's
complete incidence coordinates from its actual graph vertices, cycle edges
and outward spokes. [CycleBoundaryOrientation](CycleBoundaryOrientation.lean)
proves that cofacial ports force one uniform local orientation, at every
cycle length. A connected complement in a spherical map supplies that
cofaciality. The source-facing theorem returns both actual vertex rotations
and exact predecessor/successor port return with the same orientation choice.
The [audit](CycleBoundaryRecognitionAudit.lean) excludes the complete theorem
and catalogue certificates. The inner-pentagon rotation is thus governed by
a uniform law. [CycleSpokeConnectivity](CycleSpokeConnectivity.lean) now derives
the connected complement when all spokes meet one connected outer set.
[ElevenLobeSpokeOrder](ElevenLobeSpokeOrder.lean) computes the actual outer
return, including the longer closing gap, and uses opposite shore order to
force the pentagon's matching to be a cyclic shift or reflected shift.
Its direction agrees with every inner rotation. The explicit inputs remain
the two disjoint cycles, bijective attachment at the five inward positions,
and the alternating outer turns. The [eight-root audit](ElevenLobeSpokeOrderAudit.lean)
excludes complete theorems and catalogue certificates.
[ElevenLobeNormalizedGeometry](ElevenLobeNormalizedGeometry.lean) and
[ElevenLobeDartCoordinates](ElevenLobeDartCoordinates.lean) now retain the shared
orientation through all sixteen vertices, forty-eight darts and six ports.
The reusable [dart constructor](OpenTangleDartRecognition.lean) supplies an
exact tangle isomorphism from the actual vertex/dart bijections and their
incidence equations. Its [geometric consumer](../../../../fourcolor-classical/MettapediaFourColor/PentagonalLobeRecognition.lean)
constructs the literal patch and performs the twelve-vertex reduction.
The [twelve-root audit](../../../../fourcolor-classical/MettapediaFourColor/PentagonalLobeRecognitionAudit.lean)
requires this full reconstruction chain and excludes complete theorems and
catalogue certificates. Broader geometric supply and coverage remain open;
catalogue counts are unchanged.

[FacialCoronaTraversal](FacialCoronaTraversal.lean) now constructs an outer
arc from each neighbouring face: period `n + 3` supplies `n` outer steps.
[PentagonalCoronaGeometry](PentagonalCoronaGeometry.lean) and
[PentagonalCoronaIncidence](PentagonalCoronaIncidence.lean) apply this to a
pentagon with neighbours of lengths 5,5,5,5,6. They derive both cycles, all
outer turns and the attachment matching. [PartialCubicDartSeparation](PartialCubicDartSeparation.lean)
proves a general soundness theorem for transporting proposed dart equalities
through shared rotations and internal edge reversals. The
[finite check](PentagonalCoronaSeparationCheck.lean) covers all 720 ordered
collision/phase cases in at most six operations. [PentagonalCoronaImmersion](PentagonalCoronaImmersion.lean)
interprets these operations in the actual graph before assuming vertex
distinctness; [PentagonalCoronaNoncollision](PentagonalCoronaNoncollision.lean)
then derives distinctness from triangle-freeness supplied by the ambient
hypotheses. [PentagonalCoronaBoundary](PentagonalCoronaBoundary.lean)
confines the cut to six potential outward darts; an extra chord consumes two.
[CyclicFiveBoundary](CyclicFiveBoundary.lean) combines the forest edge bound
with cyclic connectivity, and [PentagonalCoronaChordExclusion](PentagonalCoronaChordExclusion.lean)
therefore derives outer inducedness from minimality. No exterior connectedness
or distinct attachment endpoints are needed for this chord argument. The
[face-pattern consumer](../../../../fourcolor-classical/MettapediaFourColor/PentagonalCoronaFaceReduction.lean)
performs the twelve-vertex reduction without either local geometric premise.
Its [twelve-root audit](../../../../fourcolor-classical/MettapediaFourColor/PentagonalCoronaFaceReductionAudit.lean)
checks 26,708 declarations with standard axioms only. Broader family repair,
coverage and further catalogue integration remain open. The new finite
geometric checks are counted separately; no additional original colouring
certificate is removed.

[PentagonalDiamondGeometry](PentagonalDiamondGeometry.lean) now retains only
the central pentagon and three consecutive pentagonal neighbours. The two
remaining neighbouring face lengths are unrestricted. Its
[separation check](PentagonalDiamondSeparation.lean) handles 392 collision
cases by shared dart transport and four more by excluding genuine four-cycles.
[PartialCubicDartBoundary](PartialCubicDartBoundary.lean) supplies a general
inducedness law: an even-sized injective cubic diagram with six missing
reversals, more than four vertices and enough exterior vertices has six
actual boundary darts under cyclic-five connectivity. Degree parity excludes
an unrecorded internal chord.

The [actual consumer](../../../../fourcolor-classical/MettapediaFourColor/PentagonalDiamondFaceReduction.lean)
constructs the twelve-vertex occurrence and uses the existing joint diamond
profile to replace it by four vertices. No fresh colouring certificate is
needed. The [audit](../../../../fourcolor-classical/MettapediaFourColor/PentagonalDiamondFaceReductionAudit.lean)
excludes the older corona's separate colouring checks. This strengthens the
local recognition domain and shares a proof; global coverage and additional
catalogue replacement remain open.

[MixedDiamondGeometry](MixedDiamondGeometry.lean) extends actual recognition
to a central pentagon with consecutive neighbour lengths five, six, five.
Joint dart transport and one four-edge path prove the thirteen positions
distinct. [PartialCubicDartSevenBoundary](PartialCubicDartSevenBoundary.lean)
supplies the odd-width inducedness law: seven unpaired slots really reach
the exterior when both shores are large enough and internal-six connectivity
excludes the possible five-cut.

[OpenTangleIsomorphismColoring](OpenTangleIsomorphismColoring.lean) gives
inverse whole-colouring transport, preserving each boundary colour. Its
[actual consumer](../../../../fourcolor-classical/MettapediaFourColor/MixedDiamondFaceRecognition.lean)
inherits configuration 2's existing shared repair on the recognized shore.
The [actual exterior theorem](../../../../fourcolor-classical/MettapediaFourColor/MixedDiamondExteriorClosure.lean)
now derives seven-port Kempe closure using the uniform matching codec.
[SevenPortBoundaryConnectivity](SevenPortBoundaryConnectivity.lean) permits
repeated attachment vertices; [cyclic separation](Compositional/CyclicBoundaryMatching.lean)
and [reflection](Compositional/CyclicBoundaryReflection.lean) apply at arbitrary
boundary widths of at least two. The [generic stack law](../NoncrossingMatchingStack.lean)
retains the paired choices needed by reconstruction.
[EightPortBoundaryConnectivity](EightPortBoundaryConnectivity.lean) extends
the connectivity argument to eight ports using internal-six connectivity:
seven vertices on the selected side, six on the opposite cyclic shore,
and at most eight crossing darts force the selected side to be connected.
It allows repeated attachment vertices and assumes no embedding.
[SphericalVertexLowerBound](SphericalVertexLowerBound.lean) makes the
twenty-vertex bound strict when an actual face has more than five darts.
The [joint-diamond consumer](../../../../fourcolor-classical/MettapediaFourColor/JointDiamondWiredOccurrence.lean)
derives exterior closure and wire separation at an exact embedded occurrence,
then reconstructs the original graph from the two-vertex wiring.
[OpenTangleBoundaryReindexWitness](OpenTangleBoundaryReindexWitness.lean)
supplies its exact whole-witness coordinate transport. Smaller-map class
preservation and face-pattern recognition remain open for this consumer.
[OpenTangleReplacementClass](OpenTangleReplacementClass.lean) now combines exact
ordered returns, Euler mass, connectedness and boundary-essentiality into a
single map-class preservation theorem at arbitrary finite interfaces. Both
the existing six-port reduction and the [mixed-diamond reduction](../../../../fourcolor-classical/MettapediaFourColor/MixedDiamondFaceReduction.lean)
consume it. The latter removes thirteen vertices, introduces five, and
reconstructs the source colouring from the smaller map. Every introduced
vertex is counted. Broader geometric coverage remains open; count preservation
under reduction and executable Kempe histories are not asserted.

## Independent corridor route — checkpoint of 22 September 2026

The following table describes the earlier direct Count proposal. Its open
premises are not dependencies of the completed classical assembly:

| Part | Checked result | Still needed |
| --- | --- | --- |
| Physical tree fold | Face-return data, face count and colour support agree with the actual shores of a supplied edge-leaf tree. | A globally supplied decomposition of the required bounded width. |
| D1: decomposition supply | Conditional bond laminarity; obstructions to several proposed ways of extracting bounded interfaces and long nested chains. | A construction of the required bounded-interface supply, or another source-faithful reductive construction. |
| D4: route-native finite base | A finite positional code of the fork fold, exact at every physical fork; coverage of supplied decompositions and root adequacy instantiate the decomposable base ([PhysicalForkCodeBase.lean](PhysicalForkCodeBase.lean)). The closure is sound: every root code in it is realized by a spherical cubic map ([PhysicalForkCodeSound.lean](PhysicalForkCodeSound.lean)). A verified checker replays the audit in the kernel at bound 2 (lane gate, [PhysicalForkCodeAuditTwo.lean](PhysicalForkCodeAuditTwo.lean)) and bound 3 (separate target `Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThree`). | The audit at interface bound `max w 2`, at a width `w` that D1 supplies; the closure has 1,468 states at bound 4 and at least 77,989 at bound 5. |

The final D1 checkpoint is `fd1040139`, which corrects an earlier overclaim:
site witnesses share a residual-defect minimizer, but each has its own second
matching `tau`. Their carriers are **not** thereby disjoint or laminar;
consecutive row steps cannot share `tau`. The laminarity theorem is conditional
on hypotheses which have not been supplied for all sites.

Also, arbitrarily large laminar families can be antichains. The singleton-family
counterexamples rule out a universal long-chain guarantee from family size,
even when shores may be complemented. They do not say that no laminar family
has a long chain. `CommonEdgeLaminarShoreSupply` reformulates an open supply
obligation; its equivalence to the chain version does not discharge either one.

Read the exact statements in
[PhysicalProfileFold.lean](PhysicalProfileFold.lean),
[GoertzelV24MeshBondCarrierSeparation.lean](GoertzelV24MeshBondCarrierSeparation.lean),
[GoertzelV24BondDepthObligation.lean](GoertzelV24BondDepthObligation.lean), and
[GoertzelV24DecomposableFiniteBase.lean](GoertzelV24DecomposableFiniteBase.lean).
The detailed explanatory documents are `papers/benxiv/goertzel_4cp.tex` and
`papers/benxiv/foundations/compositional-proof-spine.tex`, relative to the
repository root. The companion now opens with the completed repair; the
older corridor tables and chronological sections retain their route-specific
scope. These are companions to the primary Goertzel/Fable manuscripts.

### Fresh checkout

To reproduce the development on a new destination:

```sh
git clone --branch goertzel/proofs https://github.com/godelclaw/MeTTapedia.git MeTTapedia-4cp
cd MeTTapedia-4cp
bash lean/bootstrap_local_repos.sh
cd lean/mettapedia
lean --version
lake exe cache get
lake build FourColorLane
lake build Mettapedia.GraphTheory.FourColor.ResearchCheckpoint
cd ../..
python3 papers/benxiv/tools/gen_citation_ledger.py --check
```

Use the checked-in `lean-toolchain` (currently Lean 4.34.0-rc2) and pinned
dependencies; do not upgrade them as part of a move. Where both Lake files
exist, `lakefile.lean` is selected, not `lakefile.toml`. The bootstrap preserves
an existing dependency checkout and reports a pin mismatch instead of resetting
it. A source-host build is not evidence of a successful fresh-machine build;
run the gates on the destination too. The complete classical assembly has
additional dependency preparation and its own `kernelComplete` target; follow
the [integration build instructions](../../../../fourcolor-classical/README.md#kernel-build).

`ResearchCheckpoint` separately checks preserved supplemental results. Its
minimal-counterexample selection and abstract reflection modules refer to a
**historical, refuted closed-web target**, explicitly marked in
`GoertzelV24SourceHeadlineAssembly`. They are not the active headline and do not
revive that route. `GoertzelV24IrreducibleBaseBurden` bounds only explicit census
cardinality, not proof length or human-checkability. `GoertzelV24TubeCountGrowth`
distinguishes exact path counts from Boolean support in its specified tube.

Git carries the proof sources. Transfer primary manuscripts and any needed
private research reports separately, with appropriate permissions. Session
archives are optional historical context, not build dependencies; do not commit
them, authentication stores, or unrelated unfinished edits to the proof branch.

### Historical branches

Historical proof branch tips are preserved under `archive/goertzel-20260922/`
on the remote. These archive references preserve earlier research states;
the current development and build instructions are on `goertzel/proofs`.

## Background module guide

The older guide below describes reusable infrastructure, not the current
headline's complete dependency chain.

Read first:

- `ROADMAP.md` - detailed live status and route surface.
- `Goal.lean` - target shell claim and named oracle surfaces.
- `BoundaryChainPeel.lean` - modern algebraic home for the old
  `LeafPeelData`/`LeafPeelSumData` span-induction layer. The preferred
  aggregate interface now explicitly subsumes the old single-face peel
  interface by singleton peel sets. The face-boundary span is exposed as
  zero/addition closed, and both peel interfaces now identify the zero-boundary
  set exactly with that span once their hypotheses are supplied.
- `Orthogonality.lean` - finite-support chain-dot algebra, named
  face-boundary generator sets, and generic span-to-double-orthogonal
  propagation. The peel-data double-orthogonal theorems now use this generic
  generator-set API instead of repeating set comprehensions, and both
  single-face and aggregate peel interfaces expose their generator sets under
  structure-specific names. It also provides annihilator-facing bridges from
  generator-set membership to orthogonality of the generated span and the
  single/aggregate peel zero-boundary sets.
- `Theorem49CertificateFaceBoundarySpan.lean` - algebraic bridge from a
  `BoundaryRootedFacePeelCertificate` order to the finite face-boundary span
  generated by its listed faces. It gives later adapters a clean generator set
  and proves finite sums over listed faces lie in that span. It also propagates
  orthogonality from listed face-boundary generators to the whole
  certificate-generated span and records the corresponding finite-support
  double-orthogonal containment. Its generator-set equivalence lemmas identify
  the listed-face vocabulary with the generic image-face-boundary vocabulary,
  and its annihilator-facing wrappers turn certificate generator annihilation
  into span orthogonality without restating the listed-face generators,
  without claiming the certificate supplies the old aggregate peel interface.
- `SupportFaces.lean` - modern home for the old dynamic-forest support-face
  selector and induced support-dual adjacency vocabulary. It also exposes the
  support-dual graph as a generic `Mettapedia.GraphTheory.FiniteRelation`, so
  support-dual degrees and weak leaf/min-degree facts reuse the shared
  relation layer.
- `RotationSystem.lean` - dart/face-orbit infrastructure plus
  witness-carrying internal-face helpers, the local `InteriorFacePlanarity`
  package, and the stronger `PlanarGeometry` rotation-system layer ported from
  the old standalone package. It deliberately does not derive planarity from
  bare rotation-system data.
- `SimpleGraphRotationSystem.lean` - the first explicit bridge from
  `SimpleGraph.Dart` to the modern bare `RotationSystem` carrier. It proves the
  edge-flip/two-darts-per-edge obligations from Mathlib's dart API, but it does
  not assert vertex-rotation planarity or construct `PlanarGeometry`. It also
  records the exact stronger source object needed next: a global face-successor
  permutation whose conversion proves `RotationSystem.phi` is that successor.
  Concrete examples can build that permutation from explicit successor and
  predecessor functions via `FaceSuccessorFunctionData`.
- `PlanarBoundaryRotationSystem.lean` - bridge from the existing face-local
  `PlanarBoundaryDartSuccessorCycleEmbeddingData` layer to the global
  face-successor data needed by `SimpleGraphRotationSystem`. It records the
  exact compatibility/coverage obligation: one global dart permutation must
  agree with every local listed face successor. It also provides the
  function/predecessor version for finite examples where inverse laws are easier
  to prove than constructing an `Equiv.Perm` directly, direct forgetful bridges
  back to the face-local successor-cycle source, and explicit coverage /
  disjoint-coverage certificates for using local face cycles without hiding the
  coverage hypothesis.
- `Examples/TriangleGlobalFaceSuccessor.lean` - first active concrete example
  of the `SimpleGraph.Dart` global face-successor route: the two oriented
  cycles of the triangle supply explicit successor/predecessor functions that
  lower through the planar-boundary global-face-successor package and then to
  a bare `RotationSystem`. It exposes function-level, permutation-level, and
  face-local successor-cycle existence wrappers for the triangle, and proves
  that the two local face cycles cover the triangle darts disjointly.
- `IncidenceCounting.lean` - endpoint, face-incidence cover, at-most-two
  internal-face incidence, face-orbit toggle parity, and face-degree
  double-counting infrastructure ported from the old rotation/no-digons
  support layers. It includes the explicit-hypothesis bridge from face-orbit
  toggles to vertex-incidence parity and consumes the canonical
  `RotationSystem.InteriorFacePlanarity` package. The old endpoint-set
  injectivity theorem is represented under the honest `PlanarGeometry`
  no-parallel-edges package, not under bare rotation-system data. It also
  represents the old "interior edge has two internal faces" route as exact
  modern incidence lemmas: a non-boundary edge has the two alpha-opposite
  face-orbit edge sets as its incident faces, and under `InteriorFacePlanarity`
  / `PlanarGeometry` this yields membership in the generic
  `InteriorEdgeFacePair` interface. It also ports the old internal-face
  orbit/cardinality bridge as
  `PlanarGeometry.card_faceOrbit_eq_card_faceEdges_of_internal`.
- `RotationDiskData.lean` - disk-style rotation data, interior-dual adjacency,
  spanning-forest witness vocabulary, and no-digons as an explicit hypothesis.
  It includes the named at-most-one-shared-interior-edge elimination theorem
  for explicit no-digons hypotheses.
- `EdgeKempe.lean` - predicate-level edge Kempe components and guardrails
  ported from the old Kempe API without the unfinished parity theorem shells.
- `Shells.lean` - bundled shell hypotheses.
- `Frontier.lean` - strongest current positive and negative wrapper results.
- `Integration/GRAPH_ROTATION_LEAFPEEL_RECONCILIATION.md` - classification of
  old graph, rotation-system, disk/forest, and leaf-peel material.
- `Legacy/` - regression and obstruction records for routes that failed or
  were narrowed.

## Relationship to `lean/fourcolor/`

`lean/fourcolor/` is not merely a duplicate. It is an older standalone Lean
package built around an old proof attempt, but it also contains reusable
background theory that should be integrated here with care.

Potentially useful old background:

- `FourColor/Triangulation.lean`: `Color`, support sets, `chainDot`,
  `swap`, `delta`, `switch`, face-boundary chains, zero-boundary surfaces, and
  the old leaf-peel algebraic span-induction interfaces.
- `FourColor/Algebra/KempeSwap.lean`: swap preservation lemmas.
- `FourColor/Algebra/KempeCycles.lean`: Kempe-cycle predicates and parity
  lemmas.
- `FourColor/GraphTheory/SpanningForest.lean` and
  `FourColor/GraphTheory/WalkExtras.lean`: finite graph/walk infrastructure.
- `FourColor/Geometry/RotationSystem.lean` and related geometry files:
  planar rotation and face-orbit infrastructure.
- `FourColor/Curriculum/`: graph-theory background lessons and examples.

Old proof-attempt files with substantial gaps should not be ported as if they
were background theory. They should be archived or kept as failure records
unless a human/agent proves the missing mathematics.

## Integration Plan

1. Classify old `lean/fourcolor` files into:
   - reusable background;
   - failed proof attempt;
   - tests/scratch/hammer experiments;
   - upstream-shared package scaffolding.
2. Port reusable background into this namespace or a shared
   `Mettapedia.GraphTheory` namespace, one cluster at a time.
3. After each cluster, run the relevant Lean build and record the log.
4. Replace local duplicate definitions only after proving import compatibility.
5. Retire or gitignore the old standalone package only after useful theory has
   a new, build-checked home.

Do not describe the Four Color theorem as proved from this tree. The current
modern route is an active formal audit/proof attempt with remaining obligations.
