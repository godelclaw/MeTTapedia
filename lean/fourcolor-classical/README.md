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

The [near-linear catalogue bridge](MettapediaFourColor/NearLinearDiamondRepair.lean)
reuses this mathematics for `D0000` and `D0001` from the
[2026 catalogue](https://github.com/near-linear-4ct/reducible-configurations).
The two source files and their MIT notice are pinned in
[`tools/fourcolor/near-linear`](../../tools/fourcolor/near-linear).
Kernel checks establish the decoding, complete graph isomorphisms, every
cyclic neighbour list, prescribed internal degrees and ordered rings.
The source-to-source boundary insertion commutes with the reference insertion.
Both entries inherit the existing profile and split repair against every
Kempe-closed exterior relation; an actual repaired colouring of the second
entry also retains its GSLT insertion history.
The 23-root audit excludes every original configuration certificate and
complete Four Colour endpoint. The finite shared profile remains.
Replay with `lake build MettapediaFourColor.NearLinearDiamondAudit`; source
fidelity is checked by `python3 ../../tools/fourcolor/near-linear/audit_diamond_sources.py`.
This is exact reuse for already-covered configurations. It removes no further
dependency from the 633-entry assembly and does not verify the newer coverage
or simultaneous-repair algorithm. The
[receipt](../../tools/fourcolor/near-linear/diamond-measurements.json)
records these boundaries explicitly.

`TwoDiamondConfigurations` gives exact graph, ring and joint-boundary
semantics for configurations 3 and 6. `TwoDiamondCompositionGSLT` reconstructs
both diamonds with one shared tip colour, then interprets the reference map.
`TwoDiamondSplitRepair` transfers configuration 6's existing nine-port repair
to configuration 3 through an actual embedded boundary insertion.
`TwoDiamondAudit` checks the witness and repair dependencies; `CompleteAudit`
excludes the original certificates for configurations 1, 2, 3 and 4.
The assembly retains 629 original certificates and all 633 coverage entries.

`TwoDiamondTangle` and `TwoDiamondIntrinsic` realize configuration 3 as an
actual twenty-vertex cubic open disk, preserving the reference rotations,
internal edges and joint colouring witnesses. `TwoDiamondCycleReplacement`
replaces it by an eight-cycle in any fixed exterior, preserving the spherical
cubic connected bridgeless map class and removing twelve whole-map vertices.
The earlier colouring implication made exterior Kempe closure explicit.
`TwoDiamondHubColoring.reconstruct` now removes that extra hypothesis: a supplied
colouring of the smaller cycle map always reconstructs an original colouring.
It permits disconnected exteriors and may recolour them. The repair still
uses configuration 6's retained base certificate. Recognition of the disk in
an arbitrary source and geometric coverage remain separate obligations.

`TwoDiamondOccurrenceReduction` now transports this reduction to an actual
source graph supplied with an exact vertex-shore occurrence. The reusable
`OpenTangleVertexOccurrence` adapter constructs the complementary exterior,
preserves source vertices, rotations and edge pairs, and transports every
assembled colouring pointwise back to the source. The smaller map has twelve
fewer vertices, and every supplied smaller colouring reconstructs. Such an
occurrence therefore excludes a source from the vertex-minimal counterexample
class. No exterior-connectivity or extra normal-form premise is needed.
Deriving the occurrence from a face pattern, finding one and proving global
coverage remain separate. Replay the twelve-root dependency and axiom audit
with `lake build MettapediaFourColor.TwoDiamondOccurrenceAudit`.

`TwoDiamondBoundaryHub` replaces the disk by one ordered eight-valent hub
for reference Kempe semantics. Equal face returns preserve literal exterior
cofaciality; the spherical source gives a planar plain quasicubic reference
map. This hub is an observation device, not the smaller cubic induction map.
The cycle's supplied face colouring transports into the hub. Every repaired
hub colouring reads back to a proper physical exterior colouring with exactly
the same ordered boundary word, including the closing seam.
`OpenTangleKempeRepair.glue_of_closed_observation` then joins the compatible
witnesses. This reusable law needs a closed observation that reads back to
actual witnesses, without requiring it to describe every exterior colouring.

The [hub receipt](../../tools/fourcolor/classical/two-diamond-hub-measurements.json)
records the local gate and dependency audit. The target is
`lake build MettapediaFourColor.TwoDiamondHubAudit`.
It excludes all configuration certificates from geometry and transport,
and permits only the retained configuration-6 base in reconstruction.
No complete Four Colour endpoint is used. The separate GSLT construction
witness remains available; the new implication consumes the actual joint
colouring reconstruction. No executable physical Kempe path is extracted.
The complete assembly retains 629 original certificates and 633 coverage entries.

`SourceTaitInverse` connects physical edge colourings back to reference face
colourings. A conserved nonzero edge field on a two-sided spherical rotation
map with connected primal and facial dual has a face potential with exactly
those edge differences. The underlying `RotationConservedFacePotential`
theorem needs no cubicity; any two
potentials differ by one global colour shift, and fixing one face makes the
potential unique. In the cubic case, the existing face-to-edge interpretation
returns every supplied edge colour exactly. `TwoDiamondCycleFaceTransport`
uses this round trip on the actual smaller cycle replacement, retaining both
pieces' witnesses and the whole seam equation even for disconnected exteriors.
`SourceTaitInverseAudit` excludes complete colouring endpoints and all
configuration colour certificates. The new hub consumer uses this representation
bridge for reconstruction; the bridge itself transports a supplied witness
and removes no catalogue dependency.
The [transport receipt](../../tools/fourcolor/classical/source-tait-inverse-measurements.json)
records its nine-root audit, source/artifact hashes and program evidence.

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

`MettapediaFourColor.DiamondGeometricSupply` connects the three shared
diamond reductions to one geometric occurrence law. Three pentagonal
incidences at a five- or six-sided face supply an edge with pentagonal
flanks. In a spherical cubic all-five/six map, double counting forces such
an edge when there are fewer than 56 vertices. The actual face lengths
select the appropriate existing strict reduction under normal form.
Its minimality consumer uses no complete Four Colour endpoint or original
catalogue certificate. The
[worked argument](../../papers/benxiv/fourcolor-compositional/tube-example/README.md#geometric-supply-from-pentagonal-neighbour-density)
and [audit receipt](../../tools/fourcolor/classical/diamond-supply-measurements.json)
separate this geometric coverage from the unchanged 633 configurations and
629 original certificate dependencies of the complete assembly.

A separate [uniform corridor reduction](../../papers/benxiv/fourcolor-compositional/tube-example/README.md#two-row-deletion-with-a-cyclic-seam-shift)
now removes two rows from any recognized hexagonal tube with at least three
rows, at every width `k ≥ 2`, using a cyclic seam shift. It reconstructs
colourings and preserves the source class with exactly `4k` fewer vertices.
Its audit excludes this classical package and finite tube-stabilization
certificates. This geometric family theorem is not yet consumed by the
complete endpoints; their catalogue and certificate counts are unchanged.

A second [uniform family reduction](../../papers/benxiv/fourcolor-compositional/tube-example/README.md#a-joint-colouring-law-for-padded-cycle-caps)
replaces an `8m`-vertex padded cap by a `2m`-cycle for every even `m ≥ 2`.
The surrounding map keeps its class, and every smaller colouring reconstructs
with the exterior fixed. Exact graph-representation and GSLT consumers use
the same joint choices. The dependency audit excludes this classical package.
The [coupled physical repair](../../papers/benxiv/fourcolor-compositional/tube-example/README.md#repairing-a-constant-cap-boundary)
also handles odd widths in exactly recognized spherical shores with connected
exterior. [Actual face-trace recognition](../../papers/benxiv/fourcolor-compositional/tube-example/README.md#recognizing-caps-from-their-faces)
constructs the representation from face closures, vertex separation and short
seam faces, deriving boundary exposure by one width-independent law.
Vertex separation, exterior connectivity and global coverage remain explicit
obligations. These results add no certificate replacement to the complete
endpoints.

A [recursive capped-ladder family](../../papers/benxiv/fourcolor-compositional/README.md)
now supplies a complete construction from a two-vertex, three-edge source
base. Its end-removal operation preserves the actual parallel edge identities,
stays in the spherical map class and removes six expanded vertices per step.
Arbitrary smaller target witnesses admit the proved physical repair and
joint reconstruction; compatible reverse paths terminate by a width rank.
The [audit receipt](../../tools/fourcolor/classical/capped-ladder-measurements.json)
records this all-width recursive result. A further
[prism rung law](../../tools/fourcolor/classical/prism-rung-measurements.json)
proves that the actual spherical prism splice is exactly this smaller family
at every rim width at least three. Its arbitrary smaller target input repairs
and reconstructs through the shared law, without a new colour table.
Broader occurrence and complete-assembly integration remain open. These
results change neither the 633 coverage configurations nor the 629 original
certificate dependencies.

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
It then checks `DiamondFamilyReducibility`, the three `Sector7` modules,
`Complete` and `CompleteAudit`.
The compositional theorem does
not import the original unconditional theorem or the superseded arity-nine,
arity-ten and arity-eleven presentations. Its audit follows the dependencies
of the graph, construction and sweep endpoints, requiring 629 reference
configuration certificates, the shared diamond profile repair, split transfer
from configuration 2 to configuration 1 and configuration 6 to configuration 3,
all seven arity proofs,
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
The [degree-seven regional receipt](../../tools/fourcolor/classical/sector7-region-measurements.json)
records the replacement of sixteen hubcap fits by one. `Sector7Region`
checks the seven signed bounds `4,5,3,-2,-1,0,1` on `p7_5836r`;
`Sector7Coverage` rebuilds eight ancestors while reusing unchanged branches.
The complete endpoint audit requires all seven new bounds and excludes the
112 original member checks, sixteen fits and superseded ancestors from its
proof dependencies. The old declarations remain imported by shared modules.
This saves 105 member-check obligations; the recursive checker and all
catalogue soundness obligations remain. Replay the local comparison with
`lake build kernelSector7`.
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
configurations and 629 original certificate dependencies remain.

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
Broader-family coverage and the 633/629 catalogue counts are unchanged.

[DiamondCoupledWiring](MettapediaFourColor/DiamondCoupledWiring.lean) now gives
configuration 4's required joint contract an exact operational realization:
two free boundary wires and two cubic vertices sharing a central edge.
[DiamondCoupledWiringRotation](MettapediaFourColor/DiamondCoupledWiringRotation.lean)
constructs the actual closed graph, retaining the exterior's vertices and
rotations. [DiamondCoupledWiringWitness](MettapediaFourColor/DiamondCoupledWiringWitness.lean)
proves restriction and reconstruction of genuine colourings in every exterior
whose wire endpoints are distinct. The shared central colour is essential;
`forgetting_seam_fails` gives a kernel-checked incompatible pair of individually
valid insertion choices.

[JointDiamondTangle](MettapediaFourColor/JointDiamondTangle.lean) retains the
reference configuration's literal darts, edges, rotations and face labels.
Its `colorable_of_wiring` uses the existing shared `repair004` to reconstruct
the original fourteen-vertex piece, assuming the exterior's Kempe closure.
The two new vertices give a whole-map count difference of twelve.
[JointDiamondOccurrence](MettapediaFourColor/JointDiamondOccurrence.lean)
now transports an internal hexagon through an exact isomorphism with an
actual vertex shore. Euler counting forces more than twenty ambient vertices.
The new eight-port connectivity law and planar boundary order then supply
[physical exterior closure](MettapediaFourColor/JointDiamondExteriorClosure.lean).
[JointDiamondWiredOccurrence](MettapediaFourColor/JointDiamondWiredOccurrence.lean)
derives wire separation from triangle exclusion, builds the actual wiring,
and reconstructs the original graph from its colouring. No exterior closure
or wire-separation premise remains in `colorable_of_actual_wiring`.

[JointDiamondOccurrenceReduction](MettapediaFourColor/JointDiamondOccurrenceReduction.lean)
now proves preservation of the smaller map's bridgeless spherical cubic class,
strict decrease and exclusion from a vertex-minimal counterexample. Its cut
argument uses two old-shore extensions of the same four-port block; its complete
seam calculation removes twelve vertices, eighteen edges and six faces.
The [strict-reduction audit](MettapediaFourColor/JointDiamondReductionAudit.lean)
checks 28 roots and 28,002 dependency declarations, requiring both geometric
arguments and actual colouring reconstruction. The
[reduction receipt](../../tools/fourcolor/classical/joint-diamond-reduction-measurements.json)
records exact scope, kernel gates and the independent finite geometry replay.
No additional colouring certificate or catalogue saving is credited.

[JointDiamondFaceClearance](MettapediaFourColor/JointDiamondFaceClearance.lean)
constructs the complete ordered occurrence from the four face lengths and
spherical normal form. The fourteen vertices are distinct and all eight
candidate ports leave the core. A hidden internal chord would consume two
ports; cubic parity and cyclic connectivity force the other six to leave.
An invariant cyclic-interval label separates their actual capped face
orbits, contradicting the planar-bond theorem for the connected core and
exterior. The exact coordinate map commutes with both edge and vertex
operations, so the contradiction concerns the actual embedded graph.

The strict-reduction consumer removes fourteen vertices, introduces two,
preserves the connected bridgeless spherical cubic class, and reconstructs
colourings using the same coupled repair. Its minimal-counterexample
consumer obtains the smaller colouring from minimality. No occurrence
isomorphism, vertex-injectivity premise or outgoing-endpoint check is supplied.
The face pattern itself remains a hypothesis; broader supply and coverage
are separate tasks.

The [clearance audit](MettapediaFourColor/JointDiamondClearanceAudit.lean)
checks eighteen roots and 28,530 dependency declarations with standard
axioms only. Its [receipt](../../tools/fourcolor/classical/joint-diamond-clearance-measurements.json)
records the required geometric and reconstruction chains. The
[independent replay](../../tools/fourcolor/classical/joint-diamond-clearance-probe.json)
checks the interval law on 2,688 dart transitions and replays all 1,424
matching face patterns in 137 saved maps. The fixtures' internal-six
connectivity is not certified. No additional colouring certificate or
complete-assembly dependency saving is credited. The earlier
[conditional face audit](MettapediaFourColor/JointDiamondFaceAudit.lean)
and [receipt](../../tools/fourcolor/classical/joint-diamond-face-measurements.json)
remain historical checkpoints.

The earlier [occurrence audit](MettapediaFourColor/JointDiamondOccurrenceAudit.lean) checks twenty
roots and 23,910 dependency declarations. The
[receipt](../../tools/fourcolor/classical/joint-diamond-occurrence-measurements.json)
also records 1,424 rooted occurrences in 126 of 137 saved fullerene maps.
Every finite replacement passes the graph-class checks, while internal-six
connectivity of the fixture collection is not certified by that scan.

The [audit](MettapediaFourColor/DiamondCoupledWiringAudit.lean) checks fifteen
roots and excludes original configuration certificates, superseded repairs
and complete Four Colour endpoints. The [receipt](../../tools/fourcolor/classical/coupled-wiring-measurements.json)
records its exact scope, hashes and timings. The independent replay finds
108 joint boundary words, with 216 additional spurious words if the central
choice is forgotten. No additional catalogue dependency is replaced.

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

The degree-seven regional replacement separately changes 112 member checks
to seven, bringing the complete proof's net saving to 336. Its sixteen fit
theorems become one. These are counts of proof obligations, not primitive
recursive checker operations or a measured whole-build speedup.

All 633 configurations and all 32 discharging-rule labels remain. The shared
joint-profile certificate supplies configuration 2 and configuration 4;
configuration 1 inherits repair from 2 through the general split law.
The same law transfers configuration 6's retained base repair to configuration 3.
There are 629 original reference certificate dependencies. The common finite
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

## Near-linear catalogue family

The [near-linear source bridge](../../tools/fourcolor/near-linear/README.md)
now includes a five-entry family with a shared nine-vertex internal core.
`BoundaryTriangleRepair.repair` transfers repair through an actual boundary
triangle subdivision, using joint edge colours to reconstruct a proper
colouring after deleting the inserted vertex. Five exact source operations
consume this one law, with complete adjacency, cyclic orders and ordered
boundary correspondence checked in `NearLinearFiveData`.

`NearLinearFiveBase` retains configuration 225's rank certificate and checks
that its colour-permutation closure covers every proper fourteen-port trace.
This supplies `D0604`; `NearLinearFiveRepair` derives `D0464`, `D0465`, `D3202`
and `D0370` without further independent rank certificates. The two construction
paths from `D0370` to `D0604` commute on entire colourings, and
`NearLinearFiveGSLT.compatible_histories` constructs both histories from one
repaired witness. It does not assert confluence of independently chosen Kempe
repairs.

After preparing the reference and family artifacts described above,
`lake build kernelNearLinearFamily` replays all six new modules, ending with
the dependency and axiom audit. The audit forbids every other configuration
certificate and complete colouring endpoints. The
[measurement record](../../tools/fourcolor/near-linear/five-measurements.json)
separates this local family result from complete-assembly compression.
All 633 classical coverage entries and 629 original certificate dependencies
remain. Actual-source occurrence, geometric reduction and coverage for this
new family remain open.

`OverlappingPentagonalSectors` addresses local geometric recognition. Two
views across one actual edge have consecutive roots on a shared pentagon.
Its cyclic closure identifies their outer-corner darts. Three neighbouring
pentagon readings distributed across those views then feed the existing
physical diamond reduction, removing eight vertices with genuine colouring
reconstruction. The centre-face lengths and the remaining map are unrestricted;
the strict-reduction theorem retains the existing ambient normal-form conditions.

`lake build kernelOverlapSupply` checks this recognition theorem and its
dependency audit. It adds no reduction family or classical coverage saving:
classification of the newer paper's flat overlapping cartwheels remains open.
The [overlap explanation and measurements](../../tools/fourcolor/near-linear/README.md#recognizing-a-diamond-through-an-overlap)
state the exact scope and retained joint-profile certificate.

## Conditional flat-neighbourhood coverage assembly

`LocalCoverageAssembly.radius_twelve` proves the radius and case argument
of [Theorem 6.7(iii)](https://arxiv.org/html/2603.24880v1#S8), conditional on
three explicit local supply laws. These correspond to Lemmas 8.2, 8.7 and
8.4 of Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen and Thorup.
Every outcome retains the same occurrence witness and its whole support
when a centre moves. Degrees are actual graph degrees; finite balls use
extended graph distance, including in disconnected graphs.

```text
all degrees in B2 at most 6 --------------------> local supply in B2
otherwise find degree 7 or 8 within distance 2
                   |
             degree 7 or 8
                   |
       local supply, or degree 8 within distance 5
                   |
             local supply within B5
                   |
      transport the same witness: 2 + 5 + 5 = 12
```

`EightOverlapSupply` exposes the harder degree-eight branch: local
classification gives a supported outcome or an exceptional occurrence;
that occurrence supplies a particular second centre within distance two.
Classification at that centre either succeeds directly or supplies a
second exceptional occurrence. The joint closing law must consume both
occurrences and their placement. `eight_of_overlap` proves that these
obligations imply degree-eight supply within radius five.

`FlatNeighborhoodCoverage` instantiates this assembly on the actual
quotient-face dual. An outcome is either an overlap seam with the proved
joint pentagon readings, or an explicitly retained residual occurrence.
`residual_in_minimal_from_overlap` uses the existing strict reduction and
colouring reconstruction to exclude the first alternative in a minimal
counterexample. The residual and its full supported observations remain.

The three local supply laws are still hypotheses. The source exceptional
pattern and its specified second centre are now formalized below; promotion
of its joint core reading to a certified reduction remains open.
The charge function is an explicit input whose
connection to the published discharging rules remains open, as does the
required correspondence between the source triangulation and the dual.
No complete coverage claim follows until these obligations and the
residual exclusions are discharged.

Run `lake build kernelFlatCoverage` after preparing the existing overlap
dependencies. The dependency audit requires the radius argument, exceptional
overlap argument and actual reduction consumer, and rejects complete theorem
and original rank-certificate dependencies. This result changes neither
the 633 coverage entries nor the 629 original certificate dependencies.
See the [coverage obligation record](../../tools/fourcolor/near-linear/coverage-obligations.json)
and [measurements](../../tools/fourcolor/near-linear/coverage-measurements.json).

## Exceptional-pattern overlap geometry

`ExceptionalPattern` decodes the pinned primary `getX` function into
seventeen vertices, cyclic neighbour lists with gaps, and prescribed
degrees. An occurrence preserves all listed edges and known rotation steps
in actual ambient graph darts. The theorem `next_centered` in
`ExceptionalOverlap` proves the source-specific next-centre obligation:
vertex 14 has degree eight and lies at distance at most two from vertex 0.

Two occurrences at that prescribed placement jointly force the extra
degree-five corner of Figure 13. The proof uses the second centre's full
degree-eight cyclic word, retaining the actual shared dart fixed by the
first occurrence. Triangular face closure gives the extra edge.
`ExceptionalCore.coreHom` and `core_degrees` identify all thirteen edges and
eight prescribed degrees of the source D1774 internal graph, with support
within radius three of the first centre. `JointReading` retains both source
occurrences, their alignment and the exact core realization for subsequent
boundary reconstruction. Its whole support includes both source occurrences
and lies within radius four; the core alone lies within radius three.

The theorem `ExceptionalCore.overlap_supply` fills the next-centre and
joint closing fields for **core readings**, conditional on classification.
The close field for **certified reductions** is still open. The results
below construct the actual dual rotation and exclude both core collisions
and extra ambient core edges in the minimal regime. The full eleven-port
cyclic boundary, colouring repair, source zero-charge classification and
transport of the published observations remain explicit obligations.
The ledger remains 633 coverage entries and 629 original certificate
dependencies.

Run `lake build kernelExceptionalOverlap` with the prepared dependencies.
Its dependency audit excludes complete Four Colour endpoints and original
catalogue rank certificates. See the
[source and proof explanation](../../tools/fourcolor/near-linear/README.md#the-exceptional-overlap-and-the-d1774-core),
[source check](../../tools/fourcolor/near-linear/exception-source-audit.json)
and [kernel measurements](../../tools/fourcolor/near-linear/exception-measurements.json).


## Exceptional core: orientation, injectivity and collisions

`ExceptionalCoreOrientation` transports every source core corner to an
actual facial corner. `ExceptionalCoreLocalInjectivity` derives local
injectivity from consecutive rotation powers and the actual ambient degree.
`ExceptionalCoreCollision.source_core_alternative` consumes two aligned
source occurrences and proves: the core reading is injective, or there is
an actual nonfacial triangle within radius two of the first centre. Its
three-edge walk is a cycle. Four possible unordered collisions are checked
against the decoded core; a common flanking-corner law handles the geometric
exclusions using the retained source context.

This supplies the collision alternative without assuming a full embedded
configuration. The minimal-map consumer below now excludes the collision
branch using the established singleton-cut theorem. Inducedness, eleven-port
boundary completion, repair and zero-charge classification remain open.
No coverage entry or certificate dependency is removed.

Replay with `lake build kernelExceptionalEmbedding`. The dependency audit
checks the actual source consumer, facial transport, local injectivity and
collision laws, allowing only the standard axioms and excluding complete
Four Colour endpoints and original catalogue rank certificates. See the
[mathematical account](../../tools/fourcolor/near-linear/README.md#facial-transport-and-the-collision-alternative)
and [measurements](../../tools/fourcolor/near-linear/embedding-measurements.json).

## Exceptional core: collisions excluded in the actual minimal dual

`ActualDualRotation` constructs the simple facial dual using the original
darts, edge reversal and face permutation. Unique shared primal edges give
its faithful simple-graph backing. The graph is exactly the quotient-face
dual used by the coverage scaffold, with cyclic vertex rotations and
triangular faces proved from the original cubic rotation.

`MinimalExceptionalEmbedding.triangle_facial` consumes the existing
singleton-cut classification: in a graph-backed vertex-minimal Tait
counterexample, a dual triangle crosses three edges incident with one primal
vertex. The new actual-rotation bridge makes that triangle facial in one of
its two orientations. This contradicts the explicit nonfacial triangle
produced by any exceptional core collision.

`MinimalExceptionalEmbedding.source_core_injective` therefore derives an
injective core homomorphism from two aligned actual exceptional occurrences.
It uses their joint rotation and degree information; injectivity is not an
input. The inducedness theorem below now excludes extra ambient core edges.
The eleven-port ring, source supply from final charge, and the complete
repair contract remain separate obligations. Counts stay 633/629.

Replay with `lake build kernelExceptionalDual`. Its twelve-root audit checks
the source consumer, the actual rotation bridge and the singleton-cut proof
chain, allowing only standard axioms and excluding complete Four Colour
endpoints and original catalogue rank certificates. See the
[account](../../tools/fourcolor/near-linear/README.md#collision-elimination-in-the-actual-minimal-dual)
and [measurements](../../tools/fourcolor/near-linear/minimal-embedding-measurements.json).

## Exceptional core: exact induced adjacency

`ExceptionalCoreInduced.source_core_induced` proves that two aligned actual
exceptional occurrences in the minimal facial dual preserve and reflect
every core edge. Together with the preceding injectivity theorem, this
gives an induced realization of the eight-vertex core in the actual map.

Two uniform laws do the work. `FacialPatchInduced.corner_chain_successor`
proves that a proper interval of a cyclic vertex rotation has no additional
facial corner between its entries. If all ambient triangles are facial,
the source star therefore reflects adjacency between its neighbours.
`FacialPatchInduced.reflects_of_short_paths` extends that local reflection
to any injective patch with paths of length at most three, provided ambient
four-cycles have a diagonal. The existing minimal four-cycle classification
supplies that last hypothesis for the same actual dual.

Kernel checks establish that all D1774 core stars are proper intervals and
that the core has diameter at most three. The source consumer then applies
the shared geometric laws; it does not enumerate ambient maps or use an
original rank certificate. The boundary construction and conditional
colouring reconstruction are supplied below. Compatible colouring repair,
strict reduction and supply from zero-charge classification remain open.
Counts stay 633 coverage entries and 629 original certificate dependencies.

Replay with `lake build kernelExceptionalInduced`. The nine-root audit
requires the interval, short-path, triangle and four-cycle arguments in the
source consumer's dependencies, allowing only standard axioms. See the
[account](../../tools/fourcolor/near-linear/README.md#induced-core-from-facial-intervals-and-short-paths)
and [measurements](../../tools/fourcolor/near-linear/induced-measurements.json).

## Exceptional boundary: shared ports and exact colouring reconstruction

`ExceptionalBoundaryOccurrence.sourceHom` constructs all nineteen vertices
and every edge of the eleven-port free completion in the actual minimal
facial dual, starting from the two aligned exceptional occurrences.
`FacialStarCompletion.across_edge` proves the uniform geometric seam law:
the neighbour preceding an edge at one endpoint is the neighbour following
its reverse at the other endpoint. Eight applications make all shared
boundary readings agree. Full cyclic core stars are preserved and cover
every ambient edge incident with the core.

Inducedness and rotation injectivity exclude boundary ports from the core.
Different boundary labels may have the same ambient image. Consequently
the colouring contract uses one exterior assignment for all eleven ports,
retaining every equality caused by those identifications.

`PatchBoundaryGluing.reconstruct` is a general graph-colouring gluing theorem.
`ExceptionalBoundaryReconstruction.reconstruct` consumes the actual geometry:
a proper completion colouring agreeing with a proper exterior assignment
gives a genuine colouring of the whole dual, fixing the entire exterior.
`extension_iff` proves the converse as well. This is exact boundary semantics
for a fixed exterior assignment; the statement allows any colour type.

Existence of a compatible completion colouring, or a justified Kempe repair
reaching one, is still open for this consumer. So are strict reduction,
zero-charge classification and the integrated coverage branch. The result
removes no additional certificate or coverage entry; counts remain 633/629.

Replay with `lake build kernelExceptionalBoundary`. The fourteen-root audit
checks actual source construction, inducedness, complete star coverage and
the generic reconstruction consumer, excluding complete Four Colour
endpoints and original rank certificates. See the
[account](../../tools/fourcolor/near-linear/README.md#eleven-port-completion-and-exact-reconstruction)
and [measurements](../../tools/fourcolor/near-linear/boundary-measurements.json).

## Exceptional boundary: complete finite repair

`ExceptionalRepairCertificate.repair` proves that every proper zero-sum
eleven-port trace admits compatible repair to an actual D1774 colouring.
The certificate checks 7,381 trace representatives and 93,665 unsigned
exterior-skeleton cases. Terminal witnesses satisfy all forty-three source
edges. Every other step retains whole exterior chords and strictly decreases
the repair rank. The reusable soundness theorem quantifies over every
Kempe-closed exterior predicate.

`GraphTraceAlignment.align` aligns the entire boundary by one colour
translation. `ExceptionalRepairReconstruction.reconstruct` then invokes the
proved actual graph gluing theorem. Actual exterior Kempe closure and an
initial proper exterior trace remain explicit hypotheses; coincident boundary
images must still receive equal colours.

This is a complete finite repair check, not a case-free reduction family or
a new coverage theorem. The full finite replay took 5,964 seconds. The
twelve-root audit found only standard axioms and no complete Four Colour or
original catalogue rank-certificate dependencies. Counts remain 633/629.

Replay with `lake build kernelExceptionalRepair`. With its finite artifacts
already prepared, `lake build kernelExceptionalRepairConsumer` replays the
alignment, actual reconstruction and dependency audit. See the
[account](../../tools/fourcolor/near-linear/README.md#complete-exceptional-boundary-repair)
and [measurements](../../tools/fourcolor/near-linear/exceptional-repair-measurements.json).

## Exceptional source: compositional construction and contraction

`ExceptionalConstruction` identifies D1774 with a program of nine Y and eight
H operations, preserving all dart permutations, cyclic stars and ordered
boundary traces. The established configuration compiler proves its source
embeddability and produces an exactly checked local degree query.

`KempeRepairContract.reducible_of_repair` converts all-proper-trace repair into
the repair contract of any valid contraction. The source has a checked
one-edge contract. `ExceptionalConstructionRepair.not_fitted` excludes its
compiled query in a reference minimal counterexample through actual contract
colouring, exterior closure and reconstruction.

`ExceptionalQueryReading.actual_fitted` now derives that query fit from the
retained exceptional overlap. `ActualDualContract.singleton_colorable` supplies
the initial one-edge contract colouring directly from graph-backed vertex
minimality, on the exact dual map used by the query. `ExceptionalLocalRepair`
now completes exterior embedding and reconstruction in that same domain using
local kernel faithfulness. Zero-charge classification and geometric supply
remain open. No additional coverage entry or certificate dependency is removed.

Replay with `lake build kernelExceptionalConstruction` using the prepared
repair artifacts. Its seventeen-root audit allows only standard axioms and
excludes complete Four Colour endpoints and original catalogue ranks. See the
[account](../../tools/fourcolor/near-linear/README.md#constructed-source-local-query-and-valid-contraction)
and [measurements](../../tools/fourcolor/near-linear/construction-measurements.json).

## Actual contract witnesses from a smaller planar map

`MinimalSingletonContract.one_zero` uses the existing strict two-vertex
adjacent-pair reduction. Vertex minimality colours its smaller planar cap;
the resulting deleted-graph colouring extends to a conserved field on the
original map, with exactly the selected edge zero.

`ConservedContract.of_conserved` integrates the field into a face assignment,
preserving its value on every edge. Its exact zero set is the contract, and
every other edge remains proper. `ContractTransport` carries both the actual
assignment and the contracted edge list through exact hypermap relabelling.
`ActualDualContract.map_eq_source_relabel` proves equality of all three
permutations between the original source map and the actual facial-dual query
map. Consequently every selected dual dart has a genuine initial singleton
contract colouring in the graph-backed minimality regime.

This is a starting witness for local repair, not a proper colouring of the
whole original map. The local embedding consumer below now supplies exterior
closure and applies the checked D1774 repair. Classification and geometric
coverage remain open. The reference and graph-backed minimality definitions
are not identified by this result.

Replay with `lake build kernelMinimalSingletonContract`. The twelve-root audit
requires the smaller-map, singleton-zero, face-potential and relabelling
dependencies. It excludes complete Four Colour endpoints, original catalogue
certificates, the D1774 finite repair and reference minimal contract-colouring
theorems. Only standard axioms occur. See the
[receipt](../../tools/fourcolor/near-linear/minimal-singleton-contract-measurements.json).

## Local embedding closes the actual exceptional overlap

`ExceptionalLocalRepair.aligned_not_in_minimal` excludes the two aligned
exceptional X occurrences in the actual vertex-minimal counterexample domain.
The proof derives one explicit preembedding from the completed cyclic stars,
proves its disk injective using local kernel identity and edge reflection,
supplies the singleton contract colouring, and reconstructs an ordinary
colouring with the checked D1774 repair. Boundary-face identifications remain
permitted and are retained throughout.

`FaithfulKernelEmbedding` and `InjectiveEmbeddedRepair` isolate the sufficient
local geometric contract from the reference embedding proof. The final
`overlap_supply` theorem fills the second-centre and closing fields of the
coverage scaffold while retaining zero-charge classification as an input.
The D1774 finite repair remains; no coverage entry or original configuration
certificate is removed.

Run `lake build kernelInjectiveEmbeddedRepair`, then
`lake build kernelExceptionalExterior`.
The 29-root audit checks only standard axioms and excludes complete Four Colour
endpoints, original rank certificates and the global embedding/minimality
shortcuts. See the
[account](../../tools/fourcolor/near-linear/README.md#actual-exceptional-closing-law-through-local-embedding)
and [measurements](../../tools/fourcolor/near-linear/exceptional-exterior-measurements.json).

## Actual discharging rules and flat-neighbourhood pruning

`NearLinearRuleData` decodes all 84 oriented rules at the pinned source
revision, preserving degree intervals and cyclic gaps. `NearLinearCharge`
interprets them as actual graph occurrences. Every observed vertex lies
within radius two of both endpoints, and each rule requires a degree-five
vertex. Thus any flat centre of degree above six has a degree-five vertex
within radius two. Two distinct flat degree-eight centres have combined
external net charge exactly forty; their mutual transfer cancels.

`ExceptionalFlatCharge.overlap_supply` consumes the five-free exclusion in
the actual minimal-map domain and retains classification of the surviving
cases as an explicit input. It reuses the completed exceptional closing law.
No new configuration or coverage dependency is removed.

Run `lake build kernelNearLinearRuleData`, then
`lake build kernelNearLinearCharge` with the exceptional exterior artifacts
prepared. Source fidelity is independently checked by
`tools/fourcolor/near-linear/audit_discharging_sources.py` from the repository
root. See the [source and charge account](../../tools/fourcolor/near-linear/README.md#actual-discharge-and-a-first-classification-prune).

## Exact matching of the discharging rules

`RuleTraversal` transports source flip/rotation programs through actual
occurrences. `RuleTraversalData` checks all 638 vertex traces for the 84
pinned rules, each of length at most seven. `RuleMatcher` proves rooted
uniqueness and soundness/completeness of the executable full candidate check.
Its computed charge agrees with `NearLinearCharge.finalCharge` and feeds the
exact shared boundary budget for two flat degree-eight centres.

With `kernelNearLinearRuleData` prepared, run `lake build kernelRuleTraversal`
once, then `lake build kernelRuleMatcher`. The latter replays the generic
matcher and its dependency audit without repeating the finite trace check.
The 42-vertex experiment’s flatness remains program evidence; a local
rule-pair witness in its rotation is certified by the next target. Neither
is complete classification or coverage. See the
[account](../../tools/fourcolor/near-linear/README.md#exact-rooted-matching-and-a-concrete-joint-view-test)
and [measurements](../../tools/fourcolor/near-linear/rule-matcher-measurements.json).


## Shared charge-rule geometry

`RulePairDiamond` combines two actual pinned-rule readings around the same
six-valent vertex. Their five prescribed turns force a sixth; triangular
closure exposes the mixed-diamond face pattern. `ActualRulePairDiamond`
transports it to the original cubic map and consumes the existing strict
thirteen-to-five replacement and colouring reconstruction. Its
`right_check_false` excludes this joint rule combination in graph-backed
vertex minimality under explicit degree-five/six guards.

The same five-turn construction at a degree-five shared vertex identifies
its endpoint corners. `identified_corner` preserves that equality and
`pentagonal_of_checks` exposes the all-pentagonal diamond when the remaining
outer corner has degree five. The actual consumer invokes the twelve-to-four
replacement. `surviving_pair_degrees` combines both branches: in vertex
minimality a surviving pair with a degree-five first sender must have shared
degree five and remaining-corner degree six. No global classification premise
is assumed. `RulePairCollisionExample` certifies this second branch's local
hypotheses in the same finite rotation and consumes the uniform theorem.

`RulePairExample` certifies a nonempty instance in the saved finite rotation;
its flat charge and spherical construction remain separate program evidence.
`RulePairDiamondAudit` requires actual reconstruction dependencies and rejects
original catalogue certificates, the D1774 certificate and complete Four
Colour endpoints. The shared diamond profile remains.

Prepare the finite example with `lake build kernelRulePairExampleData`, then
run `lake build kernelRulePairDiamond` with the existing rule data, traversal
data and both diamond artifacts prepared. The
[account](../../tools/fourcolor/near-linear/README.md#two-charge-rules-force-a-shared-geometric-reduction)
and [measurement](../../tools/fourcolor/near-linear/rule-pair-diamond-measurements.json)
state the exact scope. Full surviving-profile classification remains open.

## Shared rule readings constrain the remaining charge

`RulePairCharge` handles part of the shared-five/outer-six residual. When
the second sender has degree six and the receiver has degree at least seven,
the two readings glue into the complete oriented rule `006_1`. All twenty
directed edges and fifteen turns come from the two original readings; the
identified corner is retained. `GeometryCover` separates this finite pattern
cover from agreement of the actual vertex readings and their degree bounds.

The larger rule also contains `002_2` at the same marked edge. Together with
the original `004_1`, these are three distinct one-unit contributions. A
separate endpoint lemma for the pinned rules excludes reverse transfer from
degree at least seven to degree at most six, so the three-unit bound is net.

`ActualRulePairCharge.third_and_charge` first uses the two existing diamond
reductions to obtain the residual degree profile in actual vertex minimality.
Its `flat_remainder` consumer shows that a flat degree-eight receiver has at
most seventeen units of net supply from the rest of the graph, since its
total required supply is twenty. Other incoming and outgoing transfers are
retained in this exact remainder. No independent-spoke assumption is made.

`RulePairChargeExample` supplies a nonempty instance in the saved 42-vertex
rotation. The third rule and net bound are derived from the general theorem.
Its zero final charge and exact seventeen-unit remainder remain independent
program checks. Build `kernelRulePairCharge` after the preceding rule-pair
artifacts. The dependency audit requires both actual reduction consumers and
excludes the original catalogue certificates and full Four Colour endpoints.

This adds a joint constraint for classification; it does not prove that all
flat centres contain this pair. The complete proof retains 633 coverage
entries and 629 original configuration certificate dependencies. See the
[measurements](../../tools/fourcolor/near-linear/rule-pair-charge-measurements.json).

## A paired budget retains both sender choices

`RulePairBudget.joint_bound` covers both degrees allowed for the second
sender. The first edge supplies at least four net units. A degree-six second
sender supplies at least three through the glued rule; a degree-five sender
supplies at least four through the two-unit rule `001` and its triangle
subpattern. The joint bound is therefore seven or eight, respectively.
Actual cyclic order proves the senders distinct before the contributions
are added. `Subpattern` transports complete edges and turns to the smaller
rules while retaining their actual vertex readings and degree requirements.

`ActualRulePairBudget` obtains the surviving profile through the two diamond
reductions, then applies the common seven-unit bound. Its `flat_remainder`
shows that at most thirteen net units remain outside the pair at a flat
degree-eight centre. Every other signed transfer remains in the sum.
The supplied pair is still a hypothesis; no global occurrence supply is
assumed or proved here.

`RulePairBudgetExample` checks both sender branches in the same finite
rotation and consumes the uniform theorem. Total flat charge for the
degree-six example is independently computed, not certified by this example
module; the degree-five example is not flat. Run `lake build kernelRulePairBudget`
after the preceding rule-pair artifacts. The twenty-root audit requires both
diamond reconstructions and excludes original catalogue certificates, D1774
repair and complete Four Colour endpoints. Coverage remains 633 entries and
629 original certificate dependencies. See the
[paired-budget measurements](../../tools/fourcolor/near-linear/rule-pair-budget-measurements.json).

## Changing the reduction edge removes a residual branch

`RulePairResidual.right_mixed` reads a different edge of `rule004_1`:
from its shared vertex to the remaining outer corner. If these have degrees
five and six and the sender has degree five, the two prescribed turns give
a degree-five vertex on each flank. This is precisely the existing mixed
diamond pattern. No new finite colouring certificate is introduced.

`ActualRulePairResidual.not_second_five` combines this observation with the
previous surviving-profile theorem and the strict thirteen-to-five
replacement. Consequently `second_degree_six` determines the remaining
sender degree. `forced_third` now obtains the larger `006_1` occurrence and
its net charge without requiring that degree as an input. The generic
eight-unit budget is still valid, but its degree-five branch is excluded
in the actual minimal-map consumer.

The finite degree-five budget instance also consumes this geometric law.
Build `kernelRulePairResidual` after the paired-budget artifacts. The
seven-root audit requires the actual reconstruction and excludes the full
Four Colour theorem, original configuration certificates and D1774 repair.
This closes one local degree branch; it does not supply an aligned pair
at every flat centre. Catalogue counts remain 633/629. See the
[residual measurements](../../tools/fourcolor/near-linear/rule-pair-residual-measurements.json).

## A chain repair selected by a surviving whole neighbourhood

`NearLinearChainData` identifies `D0006` with classical configuration 7, including
the whole reference construction map, every cyclic star and its ordered ring.
It proves that one actual boundary-triangle subdivision turns `D0004` into
`D0006`. `NearLinearChainRepair` then reuses `BoundaryTriangleRepair.repair`:
the retained configuration-7 certificate covers all proper nine-port traces,
and the same joint split law supplies every proper eight-port input for D0004.
No new rank or terminal-colouring table is needed for the smaller source piece.

The concrete `NearLinearChainExample` retains all thirteen source vertices in
a 42-vertex graph. All five internal cyclic stars are complete. The checked
occurrence covers every ambient edge touching the interior, so
`PatchBoundaryGluing.reconstruct` applies. `repair_actual` consumes the new
repair and reconstructs an actual graph colouring, with exterior Kempe closure
and a proper initial exterior trace left explicit. It is not an unconditional
colouring or strict-reduction theorem for arbitrary occurrences.

The motivating finite experiment has adjacent flat centres of degrees eight
and seven, no obstructing short cycle, and no mixed or pentagonal diamond core
in their radius-two union. Those whole-map properties remain independent
program checks. The Lean proofs certify source geometry, the repair transfer
and its concrete reconstruction consumer.

Replay with `lake build kernelNearLinearChain`; the
[measurement record](../../tools/fourcolor/near-linear/chain-measurements.json)
includes source pins, independent replay and the dependency audit. Only classical
configuration 7 supplies a rank certificate. The complete assembly retains
633 coverage entries and 629 original certificate dependencies. The next
obligations at that checkpoint were general recognition, the actual
exterior/strict-reduction bridge, and coverage of remaining neighbourhood profiles.

## The chain as an actual local reduction

`NearLinearChainConstruction` builds the exact D0004 disk with six Y steps
and five H steps. Its 56 darts, cyclic stars and eight ordered boundary ports
are checked against the source. `NearLinearChainContract` transports the
shared repair onto that disk and proves a concrete internal singleton
contract valid.

`NearLinearChainOccurrence` turns a graph homomorphism with five complete
core rotations and degrees into a preembedding. Core vertices must be distinct,
and boundary vertices must stay outside the core. Boundary vertices may
identify with each other. Facewise injectivity supplies a faithful kernel;
the shared kernel-to-disk theorem gives the disk injection.

`ActualChainReduction.colorable` consumes this occurrence in the graph-backed
vertex-minimal domain. The existing strict two-vertex reduction supplies a
contract colouring. The actual planar exterior supplies Kempe closure, and
`InjectiveEmbeddedRepair.colorable` reconstructs the complete colouring.
`not_in_minimal` excludes the occurrence. The caller supplies geometry alone,
with no initial-colouring or exterior-closure assumption.

`ChainReductionExample` certifies this geometric contract on the retained
42-vertex example, including a cyclic triangular rotation. It does not assert
minimality or kernel-certified global planarity of that example.

Replay with `lake build kernelChainReduction`. The
[receipt](../../tools/fourcolor/near-linear/chain-reduction-measurements.json)
and `ChainReductionAudit` distinguish this completed local consumer from the
remaining occurrence-supply theorem. The only original rank certificate is
configuration 7. No new table or uniform repair scheme is introduced, and the
complete assembly still retains 633 coverage entries and 629 original
configuration certificate dependencies.

## Recognizing the chain from a degree word

`ChainFanRecognition.not_in_minimal` recognizes the chain on the actual dual
from a degree-six centre with four consecutive neighbour degrees `5,6,5,5`.
The rotation walk supplies its three core triangles. `ChainCoreReading`
derives core injectivity and excludes extra core edges using the facial
triangle property of the minimal domain. `ChainCoreCompletion` extends the
five core stars and identifies both readings of every shared outer corner.
Its thirteen source images, including the eight boundary ports, lie within
radius two of the original centre.

`ChainCoreOccurrence` derives the full occurrence contract, allowing boundary
ports to coincide outside the core. `ActualChainRecognition` passes this
constructed occurrence to `ActualChainReduction`, which supplies the initial
colouring from strict two-vertex descent and reconstructs the original
colouring through the shared repair. No caller-supplied injectivity,
boundary completion, starting colouring or exterior closure is needed.

`ChainRecognitionExample` starts at directed edge `(39,28)` of the retained
42-vertex graph. The degree word, all five core images and all thirteen
reconstructed source images are checked. Replay with
`lake build kernelChainRecognition`; its 26-root audit retains only classical
configuration 7 as a rank certificate and excludes complete Four Colour
endpoints. The [receipt](../../tools/fourcolor/near-linear/chain-recognition-measurements.json)
records the exact hypotheses. Deriving this degree word or another reduction
from every surviving joint charge profile remains open. This recognition
result removes no catalogue entry or additional original certificate.

The continued charge-rule recognizer in
[RuleChainRecognition.lean](MettapediaFourColor/RuleChainRecognition.lean)
completes a chain from the retained degree prefix `5,6,5` and one further
five-valent neighbour. The actual minimal-map consumer uses the established
strict reduction and reconstruction; the whole patch stays within radius four
of the rule receiver. `lake build kernelChainBoundary` checks the general law,
a concrete example crossing the original radius-two view, and its dependency
audit; see the [kernel receipt](../../tools/fourcolor/near-linear/chain-boundary-measurements.json).
The [program receipt](../../tools/fourcolor/near-linear/chain-boundary-audit.json)
separates the example's flatness and global geometry checks from its Lean
recognition theorem. This is a new profile exclusion, with no coverage-count
or configuration-certificate saving.

## One fan-completion law for two degree profiles

[ThreeTriangleFan](MettapediaFourColor/ThreeTriangleFan.lean) separates the
three-triangle geometry from its prescribed degrees. A proper cyclic interval
makes the five core vertices distinct; the facial-triangle property excludes
extra core edges. [FanBoundaryScheme](MettapediaFourColor/FanBoundaryScheme.lean)
then completes full stars with a parameterized number of ports. Each port has
one defining observation, and the triangular rotation law identifies its
other reading across a shared edge. This constructs one joint boundary map,
including every source edge and full core rotation.

Both `ChainCoreCompletion` and `ExtendedChainCompletion` consume this law.
At a degree-six centre their consecutive neighbour words are respectively
`5,6,5,5` and `5,6,6,5`. The first constructs D0004's eight-port interface;
the second constructs D0006's nine-port interface. The source bridges retain
all edges, prescribed core degrees, ordered ports and cyclic turns. Boundary labels may
coincide outside the induced core.

[ActualExtendedChainReduction.not_degree_word](MettapediaFourColor/ActualExtendedChainReduction.lean)
excludes the second word in an actual graph-backed vertex-minimal
counterexample. The proof constructs the occurrence, obtains a singleton
contract colouring by strict two-vertex descent, and reconstructs through the
existing configuration-7 repair and the same planar exterior. No initial
colouring or boundary-completion assumption is supplied by the caller.
`ExtendedChainExample` checks all fourteen reconstructed images in the
retained 162-vertex rotation, within radius two of centre 48.

With the existing chain and finite-geometry artifacts prepared, replay
`lake build kernelChainRecognition`, then `lake build kernelExtendedChain`.
The latter audit checks both actual reduction consumers and their common
completion dependency; see the [receipt](../../tools/fourcolor/near-linear/extended-chain-measurements.json).
This shares the geometric argument and adds a usable recognition pattern.
It proves neither reducibility for every degree profile admitted by a scheme
nor supply of one of these two profiles in every flat neighbourhood. The
complete assembly remains at 633 coverage entries and 629 original
configuration certificate dependencies.
