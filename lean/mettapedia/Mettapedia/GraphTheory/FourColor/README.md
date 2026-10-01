# FourColor

[Two-diamond boundary elimination](TwoDiamondBoundaryElimination.lean)
composes two existing diamond summaries by retaining one shared tip colour.
It reconstructs complete witnesses for arbitrary exterior graphs, attachments
and colour alphabets, and preserves every predicate on the joint exterior.
Actual configurations 3 and 6 consume this equivalence in the classical
package. Their embedded split transfer additionally replaces configuration 3's
independent repair dependency; the latest complete audit retains 629 original
certificates and 633 coverage entries.

[Conserved face potentials](RotationConservedFacePotential.lean) give the
inverse representation bridge: a conserved Klein edge field on a two-sided
spherical rotation multigraph with connected primal and facial dual comes
from face potentials. Every literal edge is recovered, including parallel
edges. Potentials differ by
one common shift; fixing one face makes them unique. The classical package
uses this theorem to transport an existing Tait colouring to reference face
colours and back, preserving the entire supplied colouring and the joint seam
witnesses of the smaller shared-tip diamond replacement. This does not supply
an initial colouring or the remaining exterior-closure theorem.

This is the canonical modern Lean home for the godelclaw Four Color work.

## Current proof plan — 1 October 2026

Start with the [compositional proof-plan guide](../../../../../papers/benxiv/fourcolor-compositional/README.md).
It connects Goertzel and Fable's original three-level argument to the current
Lean results and identifies where the completed repair changes the proof.

The [classical integration package](../../../../fourcolor-classical/README.md)
now proves four-colourability for finite simple graphs with noncrossing plane
drawings and supplies compatible GSLT colouring witnesses for exact
constructions of every bridgeless spherical cubic source map. The checked
root is [MettapediaFourColor.Complete](../../../../fourcolor-classical/MettapediaFourColor/Complete.lean).
All 633 catalogue entries remain. The complete proof retains 629 reference
configuration certificate dependencies. A shared finite joint-profile repair
supplies configurations 2 and 4, and a general boundary-split law transfers
repair from configuration 2 to configuration 1 and configuration 6 to
configuration 3. Shared proofs also replace
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
residuals: 1,152 target vertices and 3,456 darts. The
[compact input certificates](DualTruncateResidualCertificates.lean) now
check those source and target rotations, proper source colour words, and
exact adapters in the kernel. Each target receives a genuine colouring
and compatible choices on every complete GSLT sweep through the uniform
law, without a target-colouring table. The
[input audit](DualTruncateResidualAudit.lean) excludes complete classical
endpoints. These are concrete family consumers; source-colouring existence
throughout the intended family and geometric recognition remain separate.
No coverage configuration is removed.
A [structural source supplier](DualTruncateStructuralColoring.lean) now derives
the three vertex colours under explicit graph hypotheses. Two nonadjacent
neighbours of a closing vertex share a colour; connectivity after deleting
them supplies a reverse rooted order. Earlier insertions retain an uncoloured
neighbour, and the closing insertion sees the shared colour twice. The
[general graph theorem](../CoupledThreeColouring.lean) proves this finite
Brooks argument without a source colour word or ordering certificate. A
connected noncomplete graph whose every two-vertex deletion is connected
supplies the required pair automatically.
The [cube consumer](DualTruncateCoupledExample.lean) proves actual retained
paths and reconstructs a 24-vertex target, including every complete GSLT sweep.
Its [audit](DualTruncateStructuralAudit.lean) excludes source colour-word
certificates, unfinished Brooks developments and complete Four Colour endpoints.
The [new replay](../../../../../tools/fourcolor/classical/coupled-source-colouring-probe.json)
derives fresh choices on all five residuals and finds all 14,564 two-vertex
deletions connected. Those five domain checks remain program evidence;
the structural theorem and cube domain are kernel checked.

The [cut bridge](CubicPairDeletionConnectivity.lean) now derives every
connected two-vertex deletion from simple primal degree three and cyclic
edge-connectivity at least four. Two different retained components cannot
share an outgoing dart; their total boundary uses at most the six darts of
the deleted pair. One component has at most three crossings. The existing
forest-boundary law forces cycles on both sides of its exact cut, a
contradiction. The [geometric supplier](DualTruncateCyclicSource.lean)
consumes this fact in actual source colouring, target reconstruction and
every complete GSLT sweep. A connected noncomplete source is the general
colouring domain; a specified nonadjacent neighbour pair also retains its
shared colour.

The [cut-based cube consumer](DualTruncateCyclicSourceExample.lean) interprets
a check of all 256 vertex sides as actual cyclic connectivity, derives all
28 pair deletions through the uniform law, and reconstructs the 24-vertex
target. Its [audit](DualTruncateCyclicSourceAudit.lean) checks 18 roots and
excludes source colour-word certificates and complete classical endpoints.
The [receipt](../../../../../tools/fourcolor/classical/cyclic-source-connectivity-measurements.json)
records the kernel checks and an independent cubic separator diagnostic.
The connected-deletion bridge is proved on this cut domain. The
[actual face law](DualTruncateFaceGeometry.lean) now gives an exact bijection
between target faces and the disjoint union of source vertices and source
faces. Every cubic source vertex produces a hexagon, and every source face
keeps its length. The complete joint face label supplies the Euler calculation
and separates the two facial sides of every target edge.
The [geometry consumer](DualTruncateMapGeometry.lean) lifts source walks and
establishes the target's connected, bridgeless spherical cubic map class for
a connected cubic spherical source with cyclic vertex rotations; source
bridge-freeness is unnecessary. It also combines this geometry with the
cut-based colouring and GSLT suppliers on their stated domain.

The [geometry example](DualTruncateGeometryExample.lean) derives the cube's
24-vertex, 36-edge target with six square faces and eight hexagonal faces.
Its [audit](DualTruncateGeometryAudit.lean) checks 19 roots, excluding complete
classical endpoints and source colour-word certificates. The
[receipt](../../../../../tools/fourcolor/classical/dual-truncate-geometry-measurements.json)
separates the uniform theorem and kernel cube from an independent replay of
the five larger residual sources and exact target adapters. Their source
geometry and cut domains are not yet kernel-certified. The target-only
inverse recognition below establishes source geometry on its stated face-cover
domain. Inheriting the source colouring domain and proving occurrence coverage
remain open. The complete assembly retains 633 configurations and 629 original
configuration certificates.

The [face-cover frame](DualTruncateFaceCoverFrame.lean) now selects a cyclic
frame from the unique marked facial corner at each actual target vertex.
The [inverse](DualTruncateInverse.lean) recovers the source edge flip and face
permutation from target edges and uses their rotation orbits as source
vertices. Its literal expansion preserves target alpha, rho and vertex identity
exactly. This follows the classical face-cover interpretation of leapfrog
recognition by [Fowler and Pisanski](https://doi.org/10.1039/FT9949002865).

The [inverse geometry](DualTruncateInverseGeometry.lean) proves that unmarked
hexagons give a cubic source, with spherical Euler, connectivity and one third
as many vertices. The [exact round trip](DualTruncateInverseRoundTrip.lean)
transports genuine source vertex colours. The [cube consumer](DualTruncateInverseExample.lean)
selects actual target faces, recovers an 8-vertex, 12-edge, 6-face source and
consumes that inverse in target colouring and every complete GSLT sweep.
The [24-root audit](DualTruncateInverseAudit.lean) excludes previous target-colouring
shortcuts, source colour-word certificates and complete classical endpoints.
The [receipt](../../../../../tools/fourcolor/classical/dual-truncate-inverse-measurements.json)
separates these kernel results from target-only program recognition of five
larger saved targets. No saved residual source rotation or colour word is read;
3,528 adapter darts are replayed across all six examples. The dodecahedron
diagnostic has no cover satisfying the unmarked-hexagon condition.
The earlier structural colouring consumer retains explicit source cut
hypotheses. The broader Brooks consumer below derives its domain from
target connectivity and size. This recognition is a change from
source vertex colours to target edge colours, not an unconditional Tait-to-Tait
reduction or universal coverage theorem. Catalogue counts remain unchanged.

The [source-domain example](DualTruncateSourceDomainExample.lean) recognizes
an 18-vertex target using its actual triangular and square faces, recovering
the 6-vertex triangular prism. An [exact graph-isomorphism law](CyclicEdgeCutIso.lean)
transports its cyclic three-edge cut into the recovered rotation-orbit graph.
Thus the broad face-cover, cubic, connected and spherical hypotheses do not
imply the cyclic-four condition. Nevertheless, deleting two suitable
nonadjacent neighbours leaves a connected graph, and the existing coupled
argument supplies source colours and every complete target GSLT sweep.
The [14-root audit](DualTruncateSourceDomainAudit.lean) excludes the cyclic-four
supplier, source colour words and complete classical endpoints. The
[receipt](../../../../../tools/fourcolor/classical/dual-truncate-source-domain-measurements.json)
records the kernel obstruction and independent replay. This example has
triangles and squares; it does not refute inheritance under pentagonal or
cyclic-five normal-form hypotheses. The general supplier below needs no
inherited cyclic-cut condition.
Coverage and catalogue counts remain unchanged.

The [subcubic theorem](../SubcubicThreeColouring.lean) proves three-vertex-
colourability for every finite simple graph of maximum degree three with no
four-clique. It specializes [Zając’s short Brooks proof](https://arxiv.org/abs/1805.11176):
low-degree insertion, a coupled full-path closing, or a selected closed-path
region extending a fixed exterior. The [boundary kernel](../OrderedBoundaryColouring.lean)
retains every exterior value and the shared seed choice. Path selection and
both insertion directions are proved from actual adjacency, with chords allowed.

The [target-only supplier](DualTruncateBrooksSource.lean) consumes inverse
cubicity, descended connectivity and the factor-three size law. A connected
recognized target with more than twelve vertices has a source with more than
four, excluding the four-clique exception. It receives actual Tait colours
and witnesses on every complete GSLT sweep, without source colour words or
cyclic-cut hypotheses. The [prism and cube consumers](DualTruncateBrooksExample.lean)
use this same theorem on the 18- and 24-vertex targets. Their earlier
source-specific suppliers are absent from the new proof closures.

The [24-root audit](DualTruncateBrooksAudit.lean) checks 12,375 declarations
using only the standard axioms and excludes complete classical endpoints.
The [receipt](../../../../../tools/fourcolor/classical/subcubic-source-measurements.json)
separates the general kernel theorem from independent constructive replay:
12,876 eligible labelled graphs through six vertices are coloured, 36
four-clique-containing graphs are excluded, and larger prism families are
replayed. Actual face-cover occurrence, the small exceptional target domain,
and a Tait-to-Tait strict-reduction contract remain separate obligations.
No catalogue entry or original configuration certificate is removed.

The [exact corner semantics](DualTruncateCornerSemantics.lean) now retain
all target Tait-colouring witnesses. One polygon-corner colour is kept per
source dart; the other edge colour at each expanded vertex is forced by the
two polygon colours. The joint balance equation identifies the values
computed at the two ends of a cross edge. Projection and reconstruction
are inverse, so this elimination preserves both witnesses and counts.

The [open-patch contract](DualTruncateOpenPatch.lean) applies at every size
to regions closed under source edge reversal. Its visible polygon colours
are exactly those on actual edges incident to an exterior vertex. The
extension equivalence fixes every exterior colour, including cut edges,
and supplies witnesses on every complete GSLT sweep. The
[cube consumer](DualTruncateOpenPatchExample.lean) reconstructs a fourteen-
vertex patch while fixing the ten-vertex exterior. It carries ten internal
polygon variables and reconstructs seven cross variables, replacing the
original seventeen interior edge-colour variables.

The [collapse criterion](DualTruncateCornerCoherence.lean) also makes the
retained information explicit: a compatible source vertex witness exists
exactly when the corners agree at each source vertex. With cyclic vertex
rotations, this is equivalent to vanishing cyclic differences. The cube's
reconstructed witness has a nonzero difference and cannot itself be
collapsed. Other compatible source choices still exist in this example.
The [audit](DualTruncateOpenPatchAudit.lean) excludes classical endpoints,
source-colouring suppliers and diagnostic corner data from the general law.
The [receipt](../../../../../tools/fourcolor/classical/dual-truncate-open-patch-measurements.json)
separates it from program replay of 336 source-selected patches and 353,283
actual witnesses. A smaller embedded replacement and occurrence coverage
remain open; catalogue and original certificate counts remain 633 and 629.

The [separated-forest law](DualTruncateForestCollapse.lean) proves one
geometric condition under which the source-colour summary retains every
actual witness. The source is simple and cubic with genuine cyclic
rotations; selected source vertices induce a forest, and each exterior
source vertex has at most one selected neighbour. Paired exterior corner
observations and local exterior Tait conditions supply the boundary
contract, without supplying any selected source colours. Cyclic differences
sum to zero at each vertex and agree across source edges. Their nonzero
support would have no leaf, so it cannot survive inside the finite forest.

The resulting inverse maps preserve the entire fixed-exterior colouring
fibre and its count at every family size. The
[two-cell consumer](DualTruncateForestExample.lean) selects ten actual cube
expansion vertices and fixes the fourteen-vertex exterior. Two source
variables replace eleven interior edge-colour variables and represent all
three compatible colourings. The supplied selected source values are zero.
Its construction witness composes through every complete GSLT sweep.
The [29-root audit and receipt](../../../../../tools/fourcolor/classical/dual-truncate-forest-measurements.json)
exclude complete colouring suppliers and diagnostic corner words. An
independent replay covers 56 patches and 352 witnesses, including longer
prism paths and patches in the sixty-vertex dodecahedral expansion. Those
larger fixtures are program checks. This is exact constraint compression;
a smaller embedded replacement and occurrence coverage still need proof.
No additional catalogue entry or classical certificate is removed.

The [joint two-cell law](TwoCellBoundaryChoice.lean) now states the exact
colour condition at two adjacent source vertices. If their exterior pairs
are `(a,b)` and `(c,d)`, the endpoint choices exist exactly when a pair repeats
a colour or `a+b ≠ c+d`. Distinct pairs force their third colours, which must
still differ across the shared seam. The literal eight-cycle accepts a
paired word for which these choices clash.

An [actual sixty-vertex consumer](TwoCellCycleObstruction.lean) realizes that
obstruction with a genuine spherical, connected, bridgeless cubic target
having only pentagonal and hexagonal faces. Its ten-vertex two-cell patch
has eight ordered cut ports and a proper fifty-vertex exterior, but no
colouring extends that fixed exterior. The proposed cycle accepts its cut
word. The [audit and receipt](../../../../../tools/fourcolor/classical/two-cell-replacement-measurements.json)
separate this kernel result from the independent program's complete
fifty-eight-vertex replacement and colouring. The program also tests 147
specified cycle, tree and wire candidates; none works on the full boundary
domain. Its abstract Kempe countermodel is not a realized physical exterior.
Direct cycle reconstruction therefore needs a repair of the exterior or a
different joint contract. Successful recolouring, other decompositions and
stronger geometric hypotheses remain available; no catalogue saving is
credited to this obstruction.

The [physical repair](TwoCellPhysicalKempeRepair.lean) now gives a successful
history for that same obstructed exterior. A saturated red-purple region
of seventeen original edges changes the cut word from `BBRRBBRR` to
`BBRRBBPP`. The two source choices become red and purple, and reconstruct a
proper colouring of the original sixty-vertex map while fixing every edge
incident to the exterior at its **new** value. Every faithful complete GSLT
sweep supports this reconstructed witness.

The [one-pin law](TwoCellBoundaryChoiceRepair.lean) supplies both choices
uniformly over the colour alphabet. The [physical-side law](RotationPatchKempe.lean)
reuses the common-web switch theorem on genuine retained incidences; the
[partial-source law](SourcePatchKempe.lean) supplies exterior constraints
without a complete source-colouring input. Their [audit and receipt](../../../../../tools/fourcolor/classical/two-cell-physical-repair-measurements.json)
exclude classical endpoints and complete source-colouring suppliers.
An independent replay identifies the selected region as one path and finds
four successful swaps among eight port-touching components. Universal
availability of a suitable repair, strict graph reduction and occurrence
coverage are still open. The catalogue remains at 633 configurations and
629 original certificate dependencies.

The [source-to-edge transport](DualTruncateKempeTransport.lean) now derives
the physical edge mask from any saturated partial source region, preserving
every exterior and cut observation exactly. Later steps may act on the
physical field produced by earlier steps. The [shared insertion law](TwoCellSourceRepair.lean)
uses an actual two-vertex incidence frame and a separated active pin to
construct both source choices jointly. It is independent of source size and
contains no finite graph data.

The [consumers](TwoCellSourceRepairExamples.lean) reconstruct an eighteen-vertex
prism expansion and the sixty-vertex example with this shared law. Another
sixty-vertex partial exterior needs two successive source switches in the
recorded history: its pin words change from `RBBR` to `PBBP`, then `BBBP`.
The second switch uses the state left by the first. Exact physical effects
and whole-map reconstruction are kernel proofs; the audit excludes complete
source-colouring certificates and classical endpoints. The prism belongs
to the broad spherical cubic domain, not the pentagonal/hexagonal subclass.

The [receipt](../../../../../tools/fourcolor/classical/two-cell-source-repair-measurements.json)
separates these proofs from an independent availability census of 1,298
partial source exteriors. All 302 alternating-perimeter cases admit one
separating third-colour component in that test; 78 of 996 adjacent-perimeter
cases admit no single source-component repair. The recorded two-step example
repairs one of those cases. This does not exclude other physical target-edge
operations. Universal availability, a smaller embedded operation and
occurrence coverage remain open; no catalogue entry is removed.

The [alternating-boundary theorem](SourceAlternatingBoundaryRepair.lean)
now supplies a repair under explicit geometric hypotheses: a graph-backed
spherical cubic source, distinct facial edge sides, connected full dual and
deleted shore, and four pins in the actual retained facial first-return
order, coloured `a,b,a,b`. Two third-colour paths joining both equal-colour
pairs would be edge-disjoint by proper colouring. The existing spherical
separating-trail theorem excludes that crossing, so at least one actual
component separates its pins. Its switch supplies both insertion choices,
a whole source witness, the exact physical target-edge effect, and every
complete faithful GSLT sweep. No successful component or completed source
colouring is assumed.
This is an existence and reconstruction law; it does not assert preservation
of colouring counts or lifting of every recolouring history.

The [receipt](../../../../../tools/fourcolor/classical/source-alternating-boundary-measurements.json)
distinguishes this uniform implication from finite geometry instantiations.
An independent replay computes source first-return order directly and
reconstructs all 302 alternating partial exteriors on five small sources;
251 use the first-pin branch and 51 the second. Those finite geometric
instances are program checks, not new kernel-certified fixture adapters.
Adjacent pin order, a strict smaller operation and occurrence coverage
remain open. Catalogue and original-certificate counts remain 633 and 629.

The [adjacent-pair adapter](AdjacentSourceBoundaryRepair.lean) now derives
that boundary order from the two local rotations, instead of accepting an
independent order certificate. Its graph-backed pair has four distinct
exterior pins and connected retained and deleted shores in a spherical
cubic embedding. The local rotations enumerate every deleted boundary
dart; planar complementary-shore separation reverses their order on the
retained side. Reflecting both pin pairs together preserves the shared
insertion contract. Full-dual and deleted-shore connectedness are derived,
and the resulting adapter feeds whole source and target witnesses, the
exact physical exterior switch and every complete faithful GSLT sweep.
The [audit and receipt](../../../../../tools/fourcolor/classical/adjacent-source-boundary-measurements.json)
exclude classical endpoints, complete-colouring suppliers and finite
fixtures from the uniform proof. Thirteen finite order instances on five
sources are independently replayed; their geometric hypotheses remain
program checks. No strictly smaller operation or catalogue saving is
credited.

The [03|12 source splice](AdjacentSourceSplice.lean) now completes a
smaller operation on an explicit source-witness domain. Deleting the two
source vertices and joining their actual exposed darts preserves a
spherical cubic rotation, including parallel-edge identities. Its expanded
target is bridgeless spherical cubic and has exactly six fewer vertices.
A proper three-colouring of the smaller source supplies the old exterior
and both new seam inequalities. One fixed-alphabet law leaves either a
direct joint insertion or the alternating arrangement; the derived planar
geometry supplies a separating repair in the latter case. Whole original
source and target colourings, exact physical exterior reconstruction and
every complete faithful GSLT sweep consume the same repair.
The [audit and receipt](../../../../../tools/fourcolor/classical/adjacent-source-splice-measurements.json)
check seventeen roots and exclude classical endpoints, complete-colouring
suppliers and graph fixtures. An independent replay reconstructs 2,680
smaller source witnesses on thirteen interfaces. These finite geometric
instances remain program checks. The theorem does not extract a source
witness from an arbitrary smaller target Tait colouring; recognition,
recursive closure and global occurrence remain separate obligations.
Catalogue and original-certificate counts remain 633 and 629.

The [target-witness diagnostic](../../../../../tools/fourcolor/classical/adjacent-source-target-kempe-probe.json)
now enumerates 2,920 normalized target colourings on ten smaller prism
outputs, with literal parallel edges. All computed Kempe classes reach
one of 284 coherent source images; saved paths use actual component
switches. A strict one-step decrease in incoherent source vertices fails
on six states, although their multistep repair succeeds. This is finite
program evidence for the next witness contract, with no general repair,
recursive closure or coverage theorem inferred.

The [spanning-face calibration law](DualTruncateSpanningFace.lean) now
extracts a proper nonzero source three-colouring from **every** target Tait
witness when the connected spherical source has two-sided faces, cyclic
cubic rotations and one face touching all source vertices. Corner
differences telescope on faces; the existing spherical cycle-space theorem
integrates the cross-edge field; one shared face phase makes every source
value nonzero. Re-expansion preserves all literal cross-edge colours
jointly, including parallel edges. Polygon colours may change.
The [strict splice consumer](AdjacentSourceSpanningFaceReduction.lean)
uses that extracted witness in the actual six-vertex reduction and every
complete faithful GSLT sweep. The [audit and receipt](../../../../../tools/fourcolor/classical/adjacent-source-spanning-face-measurements.json)
check twenty-one roots, exclude complete colouring suppliers and audit a
separate literal theta geometry consumer. An independent exhaustive replay
calibrates 1,488 normalized target witnesses on six recognized splice
interfaces. Four other interfaces have no spanning face and remain outside
this mechanism.

The [physical face-phase law](DualTruncateFacePhaseKempe.lean) now supplies
the missing repair history. For any source rotation and a proper source
choice sharing the input's cross field, the corner error is constant around
each face. Three saturated polygon-region switches clear its three possible
nonzero values. Every intermediate field is an actual target Tait witness;
every cross edge remains fixed. The [authored GSLT route](DualTruncateFacePhaseGSLT.lean)
retains the shared choice and actual fields. The [strict consumer](AdjacentSourceFacePhaseReduction.lean)
extracts the source witness from the repaired terminal field and reconstructs
the original map, with the full six-vertex decrease and faithful construction
sweeps. A stage may contain many connected components: it is not a bound of
three individual Kempe swaps. The [receipt](../../../../../tools/fourcolor/classical/adjacent-source-face-phase-measurements.json)
records thirty-two audited roots and a separate nontrivial parallel-edge
repair fixture. Independent replay checks 1,488 inputs, including 1,350
nontrivial repairs; up to six components occur in these small examples.
The all-width prism consumer below supplies one literal geometric family.
Broader occurrence and coverage remain separate obligations. Catalogue and
original-certificate counts remain 633 and 629.

The [literal capped-ladder family](CappedLadderRotation.lean) now gives a
complete recursive consumer. At every width `m ≥ 1`, exact face classification
proves spherical geometry, two-sided edges and a face touching all `2m`
source vertices. Parallel end edges retain distinct dart identities.
The [end operation](CappedLadderEndReduction.lean) deletes two source vertices
and sews the two exposed rail darts, producing the preceding ladder and
removing exactly six expanded vertices. Any smaller target Tait input admits
the physical repair; reconstruction fixes every retained star observation
of its terminal field. Every initial cross colour survives the repair;
initial polygon colours may change.

One [GSLT construction law](CappedLadderFamilyGSLT.lean) builds every width
from the two-vertex, three-edge source base. The compatible paths reverse
into terminating reductions with a decreasing width rank. These witnesses
also support every complete faithful construction sweep of the expanded
maps. The [receipt](../../../../../tools/fourcolor/classical/capped-ladder-measurements.json)
records forty-seven audited roots and independent replay of 340 smaller
target inputs, including 300 nontrivial repairs. No classical colouring
endpoint or saved colour table supplies the family proof. Occurrence in
broader maps and catalogue integration remain open.

The [actual prism rung family](PrismRungReduction.lean) now connects the
literal ladder to an embedded operation at every rim width `n ≥ 3`. Original
face classification proves the spherical, two-sided geometry of the
`2n`-vertex prism. Deleting an actual rung pair and sewing its four exposed
darts gives exactly the capped ladder of width `n-1`: an exact equivalence
commutes with the edge flip, vertex rotation and incidence, retaining the
parallel edge identities. The smaller geometry supplies the shared phase
law. Every smaller expanded target Tait input admits its three region
stages and joint original-source reconstruction, with exactly six fewer
expanded vertices in the reduction direction. Cross colours stay fixed
during normalization; the subsequent coupled insertion may recolour a
component of the original exterior.

The [receipt](../../../../../tools/fourcolor/classical/prism-rung-measurements.json)
records thirty-four audited roots and independent replay of 1,650 retained
darts across twenty-two widths. The 336 small target inputs include 297
nontrivial physical repairs and 88 original-exterior component repairs.
The all-width proof uses neither a classical colouring endpoint nor a
family colour table. This is geometric recognition of one family, followed
by an existing compositional witness law; it does not establish occurrence
in arbitrary spherical maps or remove a catalogue dependency.

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
