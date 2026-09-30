# Classical Four Colour and compositional reconstruction

For the connection to Goertzel and Fable's original plan, the reusable results,
and the remaining compression work, see the
[compositional proof-plan guide](../../papers/benxiv/fourcolor-compositional/README.md).

This package combines [Chris Emery's Lean port](https://github.com/corun1024/4ct)
with MeTTapedia's GSLT colouring-witness semantics. It reuses the classical
mathematics of Robertson, Sanders, Seymour and Thomas, following Gonthier and
Werner's formalization. The dependency is pinned to
`3db71e0a786a1f19be04c5266fe3d06fed216885`; `LICENSE` retains its MIT notice and
upstream attribution.

`MettapediaFourColor.Complete` proves the finite planar-graph theorem and
supplies compatible colouring witnesses along exact source constructions.
It supplies all 633 reducibility obligations and consumes all seven discharging
presentations, including the shared proofs for arities nine, ten and eleven.
These endpoints have no unproved reducibility or coverage inputs:

| Endpoint in `FourColor.CompositionalComplete` | Conclusion |
| --- | --- |
| `fourColorTheorem` | The reference's real-plane map theorem |
| `colorable_of_planeDrawing` | `G.Colorable 4` for any finite simple graph with an actual noncrossing path drawing |
| `supported_source_construction` | An exact closed construction of each bridgeless spherical cubic source map, with compatible GSLT colouring choices |
| `supported_source_sweep` | Compatible choices for any complete valid source vertex sweep |

Empty graphs, disconnected graphs and isolated vertices are included in the
plane-drawing theorem. The source-map endpoints retain literal vertices,
edges and cyclic order, including parallel edges. Compatible choices are
existential; an arbitrary partial colouring need not extend.

The lightweight `MettapediaFourColor` facade retains the reusable conditional
adapters. Import `MettapediaFourColor.Complete` explicitly for the complete
assembly. `OrbitAssembly`, `Orbit11Assembly` and `Orbit9Assembly` remain
available as the intermediate conditional results.

The source dependency is `../externals/fourcolor`, prepared by the repository's
`lean/bootstrap_local_repos.sh`. It uses Lean 4.34.0-rc2 and the same pinned
Mathlib as Mettapedia. The compatibility preparation changes the obsolete
`Mathlib.Basic.Denumerable` import to `Mathlib.Logic.Denumerable`; it changes no
proof body.

```sh
python3 lean/fourcolor-classical/scripts/prepare_reference.py
```

The preparation verifies the source revision and the complete original file
before making the import edit. It refuses unrelated local changes.

## Kernel build

First prepare the reference's generated certificates and proof artifacts, as
described in [the source and measurement record](../../tools/fourcolor/classical/README.md).
The reference uses `scripts/build_pool.py` to avoid unnecessary native C output
for its large proof certificates. Its artifacts do not have Lake's ordinary
incremental-build traces, so a normal `lake build` would repeat that work.

With the reference and the imported Mettapedia libraries already built:

```sh
cd lean/fourcolor-classical
lake build kernelAdapters
lake env lean MettapediaFourColor.lean
```

The target checks the pinned revision, compiles the adapter sources into this
package's ordinary Lean artifact directory, and audits the imported public
declarations against `propext`, `Classical.choice` and `Quot.sound`. It records
source and artifact hashes and exit statuses in
`.lake/adapter-audit/adapter-results.json`. The
[dependency replay measurements](../../tools/fourcolor/classical/dependency-artifact-measurements.json)
record the receipt upgrade for the adapters and the arity-ten presentation.
If reference artifacts live elsewhere, set `FOURCOLOR_REFERENCE_ARTIFACTS` to
that artifact directory.

To check the coverage proof that consumes shared certificates, also prepare
the reference checker modules `Present10Chk1` through `Present10Chk24`.
The nine modules reconstructed by the target need their source but do not
need their original proof artifacts. Then run:

```sh
lake build kernelOrbitPresentation
```

This target reconstructs fifteen presentation modules from exact, hashed
reference sources, in the namespace `FourColor.Orbit10`. It replaces the twenty
checks for `f10_128` and `f10_242` with the five representatives supplied by
`PeriodicHubcap` and `ReflectedHubcap`. It also removes 67 checks from 21 other
hubcaps, using semantic reflection and exchange of paired endpoints to
assemble each hubcap from retained representatives. The cover data and
split trees are preserved. Unaffected proof bodies are retained. Import names
and namespaces change so the original
and modified developments remain distinct. The generated sources,
including the reference licence and credits, are available in
`.lake/orbit-audit/src`; compilation receipts are in `orbit-results.json` in
the same audit directory.

`OrbitAssembly.fourColorTheorem_of_checks` consumes the resulting `exclude10`.
The audits verify that its dependency graph includes every semantic replacement
and the explicit colouring reconstruction, and that all 87 superseded check
declarations and the original arity-ten theorem are absent.

The next target composes this presentation with shared arity-eleven certificates:

```sh
lake build kernelOrbit11Presentation
```

It requires the reference's `Present11Defs` artifact and the shared arity-ten
package. It reconstructs all nine arity-eleven presentation modules, followed
by `Orbit11Assembly` and `Orbit11Audit`. Its generated sources and receipts are
in `.lake/orbit11-audit`. Both the graph-colouring and exact source-construction
endpoints consume all thirteen new semantic hubcaps. The audit excludes all
62 replaced arity-eleven checks, the 87 superseded arity-ten declarations and
both original arity coverage theorems.

Arity nine uses the same semantic transport and weighted-cover theorems:

```sh
lake build kernelOrbit9Presentation
```

Prepare the reference arity-nine artifacts and both earlier shared presentations
first. The target rebuilds 35 affected presentation modules and reuses 57
unchanged ones. `Orbit9Assembly` and its audit complete the 37-module gate.
The 32 selected hubcaps use 150 independent checks in place of 237, with
87 separate boundary-identity checks. Both colouring endpoints consume every
replacement. Across all three arities, 231 independent checks are replaced;
the configuration catalogue and discharging rules are unchanged.
The source pin is `orbit9-presentation-sources.json` in the measurement tools;
generated sources and receipts are in `.lake/orbit9-audit`.

## Complete assembly

After the reference, all four adapter/presentation targets above, and the
configuration-family target below succeed:

```sh
lake build kernelComplete
```

The target first audits the uncompressed reference in a separate Lean process.
It then checks `DiamondFamilyReducibility`, `Complete` and `CompleteAudit`.
The compositional theorem does
not import the original unconditional theorem or the superseded arity-nine,
arity-ten and arity-eleven presentations. Its audit follows the dependencies
of the graph, construction and sweep endpoints, requiring 630 reference
configuration certificates, the shared diamond profile repair, split transfer
from configuration 2 to configuration 1, all seven arity proofs,
the 66 named shared hubcaps, the
periodic and reflected hubcap lemmas, and the actual geometric reconstruction.
It rejects the original configuration-1, configuration-2 and configuration-4
certificates and the earlier diamond repair bodies from each endpoint's dependency closure, rejects the 236 superseded checker declarations, and checks imported public
declarations against `propext`,
`Classical.choice` and `Quot.sound`.

The driver validates the source and artifact hashes of the 87 prepared adapter
and presentation modules and the 36 configuration-family modules.
Final source hashes, artifact hashes, exit statuses
and frontend times are recorded in `.lake/complete-audit/complete-results.json`.
The original assembly measurement record is
[`complete-assembly-measurements.json`](../../tools/fourcolor/classical/complete-assembly-measurements.json).
The [joint repair record](../../tools/fourcolor/classical/diamond-joint-repair-measurements.json)
records the later family and complete-assembly checks.
The [summary record](../../tools/fourcolor/classical/diamond-summary-measurements.json)
records the common elimination law and its integrated reconstruction.
The [split repair record](../../tools/fourcolor/classical/diamond-split-measurements.json)
records the subsequent configuration-2-to-1 transfer and dependency replacement.
The reference replay, shared-presentation builds and final adapter audit are
distinct measurements; imported dependencies are reused by the final gate.

## What is preserved

The separate configuration-family gate is:

```sh
lake build kernelConfigurationFamilies
```

It reuses prepared reference artifacts and checks thirty-six modules without native
code generation. `ExecutableConfiguration` proves its executable decoder equal
to the reference pointed map; `DiamondConfigurations` supplies exact finite
presentations of configurations 1, 2 and 4. `DiamondInsertion` proves both
boundary-triangle insertions, including cyclic order, ring order and all
colouring alternatives. `DiamondInsertionGSLT` composes those alternatives into
actual reference colourings. `DiamondInsertionAudit` checks their dependency
closures and excludes classical certificates and complete theorem endpoints.
`DiamondBoundarySummary` applies one witness-level interior-elimination law to
all three literal configuration graphs and their ordered rings. Its fan model
allows arbitrary lengths and colour alphabets; reducibility is a separate
property. The eleven-root summary audit checks the generic law, graph
correspondences, boundary semantics and reconstruction into the existing GSLT
history. `DiamondJointRepair` uses this same summary to construct its terminal
colourings. The newer shared profile solver also reconstructs through this
summary, and the complete endpoint audit requires its actual graph witnesses.
`ExecutableContract` retains the reference kernel-edge order for every program
in its fragment. `ConfigurationContract` preserves exact contract-colouring
witnesses; `DiamondContract` identifies the specified contract edges and their
boundary traces for all three configurations. `DiamondContractAudit` checks
this transport independently of the existing reducibility certificates.
`DiamondJointContract` eliminates the jointly contracted interior to an exact
six-colour boundary relation and reconstructs its witnesses.
`DiamondKempeBoundary` proves that either insertion's side-edge contraction
alone fails the required Kempe trace implication. Its nine-root audit excludes
existing configuration certificates and complete theorem endpoints.
`KempeAnswerComposition` composes finite chromogram answers using the reference's
proved cover specification. `DiamondBoundaryRepair` proves the coupled
eight-port law in ten steps, without any configuration dependency.
`DiamondJointRepair` supplies twenty-three actual terminal colourings and
combines the law with exact contract elimination. Its eight-root audit excludes
existing configuration certificates and global Kempe fixed-point computations.
The [worked example](../../papers/benxiv/fourcolor-compositional/diamond-example/README.md)
explains the repair and its remaining family-extension obligations.
`KempeBoundarySplit` proves that splitting an edge colour into two distinct
nonzero colours preserves Kempe closure of the joint boundary relation.
`DiamondSplitRepair` uses that law to transfer configuration 2's existing
D-repair to configuration 1, reconstructing actual graph colourings and
validating the specified contract. Its eight-root audit excludes configuration
1's certificate and the complete theorem, and requires the retained base.
The current complete assembly retains this split-transfer law with a new base.
`DiamondProfile` solves both tips against the same centre pair.
`DiamondProfileCertificate` checks 236 trace representatives using a shared
rank on 92 joint availability profiles, including boundary length; 291 answer
references establish at most six strict descent stages. The terminal solver
constructs real interior witnesses. `KempeChordExchange.answer_exists` proves
that exchanging a chosen chord's two ends preserves an arbitrary matching
exterior, with its partner drawn from the opposite-parity active ports. This
boundary-length-independent law handles 71 of the 100 nonterminal
representatives. `KempeChordMasks` reconstructs simultaneous exchanges through
the same exterior after eliminating fixed-colour ports. Its shared finite
two-ear fact for six active ports handles another 24 representatives, with
arbitrarily many intervening fixed ports. `KempeAnchorProjection` handles the
last five cases by retaining the joint masks observed by selected anchors.
Its reconstruction proof is independent of boundary length; the five consumers
retain 44 finite joint-signature classifications. There are no remaining calls
to the old `coversRec` checker in the local profile proof.
Partner ranks, target references and 216 local ear-pair classifications remain
checked finite data; `structural_counts` and `coupled_counts` verify the actual
consumers; `anchor_counts` checks the joint signatures and their uses.
The finite planar fact is checked once for all six-step Boolean
bracket words, independently of colours and configurations. No theorem for an
arbitrary number of active ports is claimed for this two-ear certificate.
`DiamondProfileFamilyRepair` supplies the
required inputs, and `DiamondProfileReducibility` connects the law to all three
actual configurations. Its twenty-five-root audit excludes the original three
certificates, the earlier repair bodies and `coversRec` with its soundness
theorem. The complete assembly therefore
replaces three original certificate dependencies. This remains a finite core
certificate; no uniform repair for longer fans or new geometric coverage is
asserted. See [profile measurements](../../tools/fourcolor/classical/diamond-profile-measurements.json).
Shared reference modules still load the old declarations; this is not a claimed
build-time or artifact-size saving. Receipts are saved in
`.lake/family-audit/family-results.json`.

`PentagonalLobePatch` supplies a separate boundary repair for the literal
twelve-vertex dual disk of a pentagon surrounded by an eleven-edge lobe.
Its six-port trace can be made compatible with any Kempe-closed exterior
containing a proper zero-sum input. The proof produces an actual graph
colouring, using 22 terminal witnesses and nine finite answer-cover checks.
`PentagonalLobePatchAudit` checks four roots and 3,347 dependency declarations,
requires witness construction and cover soundness, and excludes configuration
certificates and complete theorem endpoints. It is checked with:

```sh
lake build MettapediaFourColor.PentagonalLobePatchAudit
lake build MettapediaFourColor.PentagonalLobeTangleAudit
lake build MettapediaFourColor.PentagonalLobePhysicalRepairAudit
lake build MettapediaFourColor.PentagonalLobeTreeReductionAudit
lake build MettapediaFourColor.PentagonalLobeEmbeddedReductionAudit
lake build MettapediaFourColor.PentagonalLobeDistinctAttachmentsAudit
```

The [worked lobe example](../../papers/benxiv/fourcolor-compositional/tube-example/README.md#from-one-seam-to-a-joint-patch-repair)
separates these kernel theorems from the independent embedded-patch recognition
and seam tests. `PentagonalLobeTangle` maps every disk colouring to an actual
sixteen-vertex cubic open tangle, preserving the six ordered boundary colours.
It glues compatible witnesses into a closed rotation-system colouring.
`PhysicalKempeBoundary` now transports actual component switching to reference
Kempe closure, preserving the common noncrossing matching and reconstructing
every chromogram answer. Its embedded consumer uses the existing spherical
six-port cyclic-bond theorem. Cubic incidence supplies the proper zero-sum input.
`PentagonalLobePhysicalRepair` therefore needs one proper exterior colouring,
cubicity and physical noncrossing to colour the sewn map. Its seven-root audit
checks 21,333 dependency declarations and excludes catalogue certificates and
complete theorem endpoints.

`PentagonalLobeTreeGeometry` proves a contextual geometric replacement:
a particular four-vertex path-shaped cubic tree has the same ordered six-port
return and Euler contribution as the sixteen-vertex patch. In any connected
exterior where the original sewing is a connected bridgeless spherical cubic
map, the replacement stays in that class. Six faces disappear and all exterior
dart cofaciality is preserved. The whole map loses twelve vertices, with all
four introduced vertices included in the count.

`PentagonalLobeTreeReduction` connects this geometry to joint repair. Under
physical noncrossing, every colouring of the smaller map reconstructs to a
colouring of the original. Cubicity is inherited from the source; vertex
minimality can supply the smaller colouring. The audit excludes complete
Four Colour endpoints and catalogue reducibility certificates. The new
[measurement record](../../tools/fourcolor/classical/pentagonal-lobe-tree-measurements.json)
records these statements and their exact scope.

Independent tests cover all fourteen four-vertex trees in 29 supplied maps:
all 406 replacements preserve simple, connected, bridgeless spherical cubic
geometry. The theorem covers the specified path-shaped tree and permits
multigraph exteriors.

`PentagonalLobeEmbeddedReduction` applies it to an actual recognized vertex
shore of a spherical cubic simple graph. The recognition isomorphism preserves
vertices, internal darts, ports, edge pairing and rotation. With two-sided
faces and connected exterior, the theorem derives the exterior's opposite
cyclic order, physical noncrossing and dual connectedness. It proves the
patch connected and transports the repaired colouring to the original ambient
map. `Embedded.not_in_minimal_counterexample` excludes such an occurrence
without invoking the complete theorem. The
[embedded receipt](../../tools/fourcolor/classical/pentagonal-lobe-embedded-measurements.json)
records its dependency audit and exact hypotheses.

`PentagonalLobeDistinctAttachments` derives exterior connectedness from the
six distinct exterior attachment vertices and cyclic edge-connectivity at
least four. Minimality supplies the cut bound. The reusable
`MatchingBoundaryConnectivity` theorem covers every nonempty side of a finite
cubic graph under that cut bound, with fewer than eight outgoing darts and
distinct initial vertices: two components would each contain a cycle and
require at least four disjoint boundary edges. Its
[receipt](../../tools/fourcolor/classical/pentagonal-lobe-attachments-measurements.json)
records the actual strict-reduction consumer.

`PentagonalLobeMinimalExterior` now removes the distinct-attachment condition
for the minimal-counterexample application. A side with at most six ports,
more than two vertices, and a complementary cycle is connected in a cubic
graph with cyclic cuts of size at least four. Euler and minimum face size
leave at least four exterior vertices, and the patch's cycle follows from
cubic incidence. Minimality supplies both geometric bounds. The theorem
`Embedded.not_in_minimal_counterexample_of_recognition` therefore needs only
the exact local occurrence and minimality; an exterior root is also derived.
The [receipt](../../tools/fourcolor/classical/pentagonal-lobe-minimal-exterior-measurements.json)
records eleven audited roots, including the strict whole-map reduction and
colouring reconstruction. The two-cycle recognition bridge below now
constructs the local occurrence. Broader supply and coverage remain open.
The complete assembly and credited certificate savings are unchanged.

The [cycle-recognition component](../mettapedia/Mettapedia/GraphTheory/FourColor/CubicCycleIncidence.lean)
now derives all local rotations and exact port return from cycle vertices,
cycle edges and outward spokes in a spherical cubic source with connected
complement. It works at every length and retains one shared orientation
choice. The [audit receipt](../../tools/fourcolor/classical/cycle-boundary-recognition-measurements.json)
separates this uniform geometric law from the independent 3,840-case
pentagon-spoke experiment. The [spoke-order theorem](../mettapedia/Mettapedia/GraphTheory/FourColor/ElevenLobeSpokeOrder.lean)
now proves its order constraint in actual spherical sources: two disjoint
cycles with the five inner spokes at the inward lobe positions and the
stated outer turns force a cyclic or reflected matching, coupled to the
inner rotations. Complement connectivity is derived from the outer cycle;
the longer closing gap is included in the exact return. The
[receipt](../../tools/fourcolor/classical/eleven-lobe-spoke-order-measurements.json)
records the eight-root audit.

[PentagonalLobeRecognition](MettapediaFourColor/PentagonalLobeRecognition.lean)
now completes the family bridge. `recognized` constructs the full literal
patch isomorphism from that independently stated two-cycle geometry.
`strict_reduction_of_geometry` gives an actual smaller map in the same
bridgeless spherical cubic class, with twelve fewer vertices and genuine
colouring reconstruction, under minimum face size five and cyclic
edge-connectivity at least four. `not_in_minimal_counterexample` derives
those exterior conditions from minimality. Repeated attachment endpoints
are permitted. The [coordinate codec](MettapediaFourColor/PentagonalLobeCoordinates.lean)
preserves every vertex, edge reversal, rotation and exposed port. Its flat
permutation tables are kernel-checked. The [twelve-root audit](MettapediaFourColor/PentagonalLobeRecognitionAudit.lean)
checks 26,523 dependency declarations and excludes the complete theorem,
original catalogue certificates and diamond reducibility. The
[receipt](../../tools/fourcolor/classical/pentagonal-lobe-recognition-measurements.json)
records the exact scope and artifacts. General stopping-lobe supply,
broader families, coverage and further certificate replacement remain open.

[PentagonalCoronaFaceReduction](MettapediaFourColor/PentagonalCoronaFaceReduction.lean)
derives the two-cycle geometry from an actual pentagon surrounded by four
pentagons and one hexagon. Face traversal constructs the edges, turns and
spoke matching. A general dart-separation theorem, a finite check of 720
ordered collision/phase cases, and an exact actual-graph realization now
prove distinctness of the sixteen traced vertices. Cyclic-five connectivity
excludes outer chords: a chord leaves at most four outward edges, while the
central cycle and at least four exterior vertices would make this a forbidden
cyclic cut. Minimality supplies the ambient bounds. Neither distinctness nor
outer inducedness is required as a local input. The consumer gives the
twelve-vertex strict reduction and genuine reconstruction from the six face
lengths and ambient normal form.
Its [twelve-root audit](MettapediaFourColor/PentagonalCoronaFaceReductionAudit.lean)
checks 26,708 declarations, excluding complete theorems and catalogue
certificates. The [receipt](../../tools/fourcolor/classical/pentagonal-corona-noncollision-measurements.json)
records the theorem, artifact hashes and geometric checks. Original certificate
counts and finite colouring checks are unchanged. Broader family coverage
and integration of further complete-proof replacements remain open.

[PentagonalDiamondFaceReduction](MettapediaFourColor/PentagonalDiamondFaceReduction.lean)
now supplies a smaller shared core. A central pentagon with three consecutive
pentagonal neighbours suffices; the other two neighbouring face lengths are
unrestricted. Actual face traversal constructs twelve distinct vertices and
six genuine ports. The [shared replacement theorem](MettapediaFourColor/SixPortTreeReplacement.lean)
replaces this core by four vertices, preserves the ambient map class and
reconstructs a colouring jointly with the exterior. The colouring proof is
`DiamondProfileReducibility.repair001`, already used by the classical assembly.

The earlier six-face corona exclusion is a corollary. In this application,
the separate 22 terminal-colouring and nine answer-cover checks disappear
from the dependency closure. The old twelve-vertex decrease remains available
separately; the broader theorem decreases the whole map by eight. The
[eighteen-root audit](MettapediaFourColor/PentagonalDiamondFaceReductionAudit.lean)
checks 27,238 declarations and excludes those older checks, original catalogue
certificates and complete Four Colour endpoints. Its
[receipt](../../tools/fourcolor/classical/pentagonal-diamond-measurements.json)
separates this application-level sharing from catalogue compression: all 633
configurations and 630 original certificate dependencies remain.

The [independent replay](../../tools/fourcolor/classical/pentagonal-diamond-probe.json)
finds 318 matching central faces across 75 of the same 137 maps, compared
with 76 faces across 29 maps for the earlier pattern. It also records why
retaining the larger interface was too strong: the eight-port full-repair
test leaves an abstract closed obstruction, while the smaller diamond
reduction succeeds under the proved source hypotheses. No claim of universal
pattern occurrence follows from the census or the local reduction.

[MixedDiamondFaceRecognition](MettapediaFourColor/MixedDiamondFaceRecognition.lean)
now constructs configuration 2's thirteen-vertex, seven-port occurrence from
a central pentagon and consecutive neighbour lengths five, six, five.
The other two neighbours remain unrestricted. At this odd boundary width,
cyclic-five connectivity and degree parity alone allow a hidden five-cut;
cubic-dual internal-six connectivity excludes it. Minimality supplies that
stronger ambient hypothesis. Vertex distinctness, the complete dart map and
all seven outgoing ports are derived from the actual face pattern.

[OpenTangleKempeRepair](MettapediaFourColor/OpenTangleKempeRepair.lean) transports
whole colouring witnesses and their ordered boundary observation through
the constructed isomorphism. The actual region therefore inherits
`DiamondProfileReducibility.repair002`. The context theorem glues compatible
interior and exterior witnesses at arbitrary boundary width.
[MixedDiamondExteriorClosure](MettapediaFourColor/MixedDiamondExteriorClosure.lean)
now derives physical Kempe closure of the actual seven-port exterior from
its connected shores and cyclic boundary order. It allows repeated exterior
attachment vertices. [MixedDiamondFaceReduction](MettapediaFourColor/MixedDiamondFaceReduction.lean)
now supplies the smaller map: replace thirteen vertices by the five vertices
of [SevenPortTree](MettapediaFourColor/SevenPortTree.lean), with all seven seam
edges retained. The connected bridgeless spherical cubic class is preserved.
A colouring of this smaller map restricts to a genuine exterior witness;
the existing joint repair reconstructs the source colouring. The whole-map
decrease is eight, and minimality excludes the face pattern without assuming
an exterior colouring. Exact representation changes give a bijection of
colouring assignments; this reduction asserts colourability reconstruction,
with no counting or executable-history equivalence claimed.

The [strict-reduction audit](MettapediaFourColor/MixedDiamondFaceReductionAudit.lean)
checks fourteen roots and 28,102 dependency declarations. It requires the
actual recognition, seven-port exterior closure, whole-map count, shared
configuration-2 repair and the common map-preservation theorem now also used
by the six-port reductions. Its [receipt](../../tools/fourcolor/classical/mixed-diamond-reduction-measurements.json)
records the exact assumptions, artifact hashes and bounded geometry replay.
Broader-family coverage and the 633/630 catalogue counts are unchanged.

The [recognition audit](MettapediaFourColor/MixedDiamondFaceRecognitionAudit.lean)
checks 21 roots and 27,512 dependency declarations using only the standard
three axioms. The [receipt](../../tools/fourcolor/classical/mixed-diamond-measurements.json)
and [independent replay](../../tools/fourcolor/classical/mixed-diamond-probe.json)
record 468 geometric separation cases and 1,059 rooted occurrences across
130 of 137 existing fixtures. No new colour certificate, catalogue removal,
complete-proof dependency replacement or universal coverage is claimed.

[KempeMatchingChromogram](MettapediaFourColor/KempeMatchingChromogram.lean)
and [KempeMatchingReconstruction](MettapediaFourColor/KempeMatchingReconstruction.lean)
now work at every finite width. One noncrossing-stack proof replaces the
six-port matching enumeration and retains the original paired choices for
every answer. The physical separator's cyclic-arc witnesses are also uniform;
the earlier five-port enumeration is removed. The
[twenty-root audit](MettapediaFourColor/MixedDiamondExteriorClosureAudit.lean)
checks the complete chain through the actual mixed-diamond exterior, and the
[receipt](../../tools/fourcolor/classical/uniform-kempe-measurements.json)
records separate proof, classification and catalogue metrics. No additional
configuration certificate is removed by this boundary extension.

The hypermap dictionary preserves actual dart permutations, components and
planarity. Reconstruction retains compatible disk and exterior colourings as
GSLT witnesses and glues them into an explicit ambient colouring. The graph
bridge preserves every supplied dart colour while descending to a colouring
of the original simple graph; isolated vertices receive zero.

`HypermapTransport` relabels darts through an equivalence, preserving all
three permutations, components, planarity and face colourings. Relabelling
through a finite ordinal makes the catalogue theorem available for finite
dart carriers in any Lean universe.

`SourceTait` connects that theorem to the original spherical cubic map class.
The source Euler equation and connected cyclic rotations imply reference
planarity; the existing bridge theorem supplies two-sided faces. Adjacent
face colours determine nonzero edge differences, which descend through the
existing dart-colouring adapter to the original literal edges, including
parallel edges. The exact colour formula is proved at every dart.

`CompositionalComplete.supported_source_construction` supplies a closed
GSLT construction trace, an exact geometric model of the source, and
compatible colouring witnesses. All reducibility and presentation obligations
are supplied by the complete assembly. The dependency audit follows this
source-construction endpoint independently of the plane-drawing endpoint.

The reference's Kempe-closure argument selects compatible assignments using
classical choice. The adapter does not extract an executable Kempe-move path.

`PlaneDrawing` gives a second graph endpoint using actual noncrossing paths in
the real plane. Its data are distinct vertex positions, an injective continuous
path for each oriented edge, reversal of paths when edges are reversed, no
vertices in edge interiors, and disjoint interiors for different unoriented
edges. It has no rotation, Euler characteristic, or colourability field.

The proof cuts every edge at its midpoint. The closed half-edges incident to
each vertex form a compact site; deleting their outer midpoints gives its
connected, dense exclusive core. The regions strictly nearest to these sites
are open, connected and pairwise disjoint. An edge midpoint is a non-corner
contact of exactly its endpoint regions, so their map colours give different
vertex colours. Empty graphs, disconnected graphs and isolated vertices need
no extra assumptions. The region map can have extra adjacencies; the transfer
uses preservation of every original graph edge, rather than an isomorphism
of adjacency relations.

`NearestRegions.isConnected_region` proves the metric part in any real normed
space, without convexity of the sites. `CompactPlaneMap` proves the precise
contact-to-adjacency and colouring transfer. `PlaneDrawing.colorable` constructs
all their geometric inputs from the drawing and concludes Mathlib's
`SimpleGraph.Colorable 4`, assuming the plane-map Four Colour theorem.
`CompositionalComplete.colorable_of_planeDrawing` supplies that plane-map
theorem from the complete GSLT reconstruction and coverage proof. The dependency
audit checks that the graph endpoint consumes both the geometry and the shared
certificates. Its only graph-specific hypothesis is the supplied drawing.

## Compression baseline

The reference contains 633 configurations, rings up to size 14, and 32 published
discharging-rule labels. Its own packed-data and uniform checker techniques
belong to the baseline.

`HubcapOrbit.oneEntries_fit_periodic` assembles a hubcap from one certificate
per distinct rotated boundary input. Its consumer `PeriodicHubcap.succeeds`
closes the reference's part `p10_127r` with two representative checker
computations instead of the ten used for `f10_128`. A finite kernel check also
verifies the equalities of the rotated parts; the general lemma transports
the two certificates to all ten positions. The original ten check theorems
are not imported by this consumer. `HalfTurnHubcap.succeeds` applies the same
lemma to `p10_241r`: its period-five boundary reduces the ten checks for
`f10_242` to five representatives, again with a separate finite check of the
rotated-part equalities.

`ReflectedHubcap` further reduces those five representatives to three.
`ChargeBound` converts a checker result into a bound on the actual edge
charge. The reference's mirror-map and charge-invariance theorems transport
this bound through reflection; a general summation lemma combines bounds
around the hub to rule out a positive charge. This proof does not assume
that the Boolean checker commutes with reflection. The intermediate
`HalfTurnHubcap` remains available as a comparison, but the coverage proof
now consumes the stronger semantic certificate.

`HubcapCharges` separates the weighted-cover argument from its graph input.
Its arithmetic theorem applies to arbitrary integer charges constrained by
single-edge or paired-edge bounds. `PairChargeBound.of_check` supplies semantic
paired-edge bounds, and `Hubcap.successful` combines these with transported
single-edge bounds. `PairChargeTransport` proves that paired bounds also
transport through reflection and exchange of endpoints, with the part and
offset changed together. The combined symmetries remove 67 computations
across 21 hubcaps, reducing their 188 checks to 121. Every replacement is
verified as a dependency of both the graph-colouring and source-construction
endpoints.

The reduction of 82 independent discharging checks is consumed by the
complete arity-ten coverage proof and the conditional `OrbitAssembly` endpoint.
Its 2,580 explicit checker obligations become 2,498, with 69 separate finite
checks of boundary-input identities or classifications.

`Orbit11Assembly` composes that result with thirteen arity-eleven hubcaps whose
140 computations become 78. The entire arity-eleven presentation goes from
571 to 509 independent checks, with 62 separate full-input reflection identities.
Across both arities, 3,151 checks become 3,007: 144 independent computations
are replaced, and 131 identity or classification checks are counted separately.
Both colouring endpoints consume all replacements.

The complete assembly additionally consumes the arity-nine sharing, where
8,212 independent checks become 8,125. Across arities nine through eleven,
11,363 checks become 11,132, with 218 separate finite identity or classification
checks. The unconditional endpoints consume all 231 replacements.

All 633 configurations and all 32 discharging-rule labels remain. The shared
joint-profile certificate supplies configuration 2 and configuration 4;
configuration 1 inherits repair from 2 through the general split law.
There are 630 original reference certificate dependencies. The common finite
profile explanation retains cover data. A uniform broader core reduction and
new geometric coverage remain open.

`KempeBoundaryMerge`, `BoundaryEarRepair`, `BoundaryEarGSLT` and
`DiamondEarFamily` establish a common contextual family theorem. Adding a new
vertex to the ends of a retained boundary edge has the exact joint split
semantics. Repair survives arbitrary repetitions at the first boundary edge,
with genuine intermediate colouring witnesses and one extra vertex per step.
All three diamond cores consume the same law; configuration 4 retains its
coupled input. `DiamondEarFamilyAudit` checks twelve roots and excludes complete
theorem dependencies and additional configuration certificates. This result
removes no additional certificate and supplies no embedded-map recognition or
coverage theorem. See the [ear measurements](../../tools/fourcolor/classical/diamond-ear-measurements.json).
Exact counts
and measurement scope are recorded in the
[compression ledger](../../tools/fourcolor/classical/compression-ledger.json).
The small pilot shows no measured runtime or artifact-size improvement after
including the generic lemma; those savings are recorded as zero.

A compression result must identify the uniform lemma, the configurations or
checks it replaces, and the kernel-checked consumer. Removing configurations
from the unavoidable set additionally requires a new coverage proof. Certificate
sharing and a smaller unavoidable set are recorded separately.
