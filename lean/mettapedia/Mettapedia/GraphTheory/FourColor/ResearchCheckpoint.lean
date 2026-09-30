import Mettapedia.GraphTheory.FourColor.PaddedCycleCapAudit
import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkChecks
import Mettapedia.GraphTheory.FourColor.BoundaryTriangleAlternatives
import Mettapedia.GraphTheory.FourColor.SphericalProtectedLinkedBand
import Mettapedia.GraphTheory.FourColor.FaceRegionCurvature
import Mettapedia.GraphTheory.FourColor.FaceRegionSweep
import Mettapedia.GraphTheory.FourColor.FaceBoundaryJunctions
import Mettapedia.GraphTheory.FourColor.FaceColourTransfer
import Mettapedia.GraphTheory.FourColor.FacePathExtension
import Mettapedia.GraphTheory.FourColor.FaceExposedDegrees
import Mettapedia.GraphTheory.FourColor.FacePairColourExtension
import Mettapedia.GraphTheory.FourColor.FaceOrderExchange
import Mettapedia.GraphTheory.FourColor.FaceSweepEdgeBudget
import Mettapedia.GraphTheory.FourColor.ThreeTwoFaceTransfer
import Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceExample
import Mettapedia.GraphTheory.FourColor.ThreeTwoFaceRepair
import Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceKempe
import Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitchGeometry
import Mettapedia.GraphTheory.FourColor.FaceMatchingCapColouring
import Mettapedia.GraphTheory.FourColor.AdjacentPairFacialTail
import Mettapedia.GraphTheory.FourColor.AdjacentPairLockedGeometry
import Mettapedia.GraphTheory.FourColor.DeferredFaceChoiceExample
import Mettapedia.GraphTheory.FourColor.FaceKempeRepair
import Mettapedia.GraphTheory.FourColor.ShortStepKempeCounterexample
import Mettapedia.GraphTheory.FourColor.LockedKempeOrbitGeometry
import Mettapedia.GraphTheory.FourColor.FacialRollbackKempeRepair
import Mettapedia.GraphTheory.FourColor.FacialRollbackLength
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCountGrowth
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonTubeSaturation
import Mettapedia.GraphTheory.FourColor.OddCappedTubeSaturation
import Mettapedia.GraphTheory.FourColor.ZigzagRingTwoColour
import Mettapedia.GraphTheory.FourColor.ZigzagTubeCompression
import Mettapedia.GraphTheory.FourColor.ZigzagRingGeometry
import Mettapedia.GraphTheory.FourColor.ZigzagTubeStructural
import Mettapedia.GraphTheory.FourColor.ZigzagTubeReplacement
import Mettapedia.GraphTheory.FourColor.ZigzagTubeBoundaryAudit
import Mettapedia.GraphTheory.FourColor.InducedCycleLayer
import Mettapedia.GraphTheory.FourColor.FacialCycleTangle
import Mettapedia.GraphTheory.FourColor.FacialCycleChord
import Mettapedia.GraphTheory.FourColor.HexagonalTubeAudit
import Mettapedia.GraphTheory.FourColor.BufferedFrontierConstruction
import Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT
import Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition
import Mettapedia.GraphTheory.FourColor.VertexConstructionLiftBoundary
import Mettapedia.GraphTheory.Representation.ColoringTransport
import Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation
import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeShore
import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeCountermodel
import Mettapedia.GraphTheory.FourColor.Compositional.KempeChannelSplice
import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeMateDependence
import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempePlaneWitness
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalCounterexampleSelection
import Mettapedia.GraphTheory.FourColor.GoertzelV24IrreducibleBaseBurden
import Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination

/-!
# Supplemental research checkpoint

Diamond-interior elimination gives an equivalence of actual colouring
witnesses for an arbitrary boundary graph and attachment relation. Both tips
retain their choices conditioned on the same distinct pair of centre colours;
every predicate on the joint boundary assignment is preserved. The classical
package instantiates this law on configurations 1, 2 and 4 and uses it to
reconstruct the terminal witnesses of the configuration-4 boundary repair.

An explicit build root for preserved results outside the active headline.
The minimal-counterexample selection module imports the historical
`GoertzelV24SourceHeadlineAssembly` and its abstract reflection interface.
That assembly documents its refuted closed-web target and is retained as a
conditional template, not as the current proof route.

The census bounds concern enumeration size only. The tube count results
concern the specified transfer relation, not every possible interface model.
The buffered construction gives actual colourings for a family with changing
width, including neighbouring split/merge cells. It does not supply a
decomposition of arbitrary maps into that family.
The relational GSLT interpretation retains compatible colouring witnesses,
and literal serial gluing gives an equivalence of colouring fibres. The raw
vertex-code language represents every map in the source class exactly;
the separate classical assembly supplies compatible witnesses on those
source routes. Uniform corridor coverage remains a separate research question.
An explicit admissible word refutes unrestricted lifting through every merge.
Simple-graph layout conversions transport existing vertex-colouring witnesses
and boundary counts exactly. This transport does not create an initial
colouring or supply an embedding-aware Tait-colouring representation.
A nonempty five-port boundary language avoiding the pentagon is exactly the
thirty rejected words. This language itself satisfies the abstract parity,
colour-relabelling and noncrossing component-union closure rules. The physical
spherical-shore adapter retains all geometric hypotheses and a starting
proper colouring; excluding the exceptional physical support remains open.
The physical Kempe-channel update is exactly a composition of two cut pieces
of the common graph, retaining their internal attachment darts. An explicit
connected planar five-pole refutes determining this update from the boundary
word and the three boundary connectedness relations, even for the same
selected component. Its literal endpoint graph, rotation system, boundary
order, proper colourings and channel connectedness are linked by exact
transport theorems. Neither a bound on the attachments nor a general escape from
the rejected pentagon support follows from these results.
For every circumference at least three, the complete zigzag-ring support
stabilizes after the explicit bound `2 * (k * (k - 1))`: full-colour words
are classified by multiplicities, and missing-colour words by cyclic rotation.
The quadratic bound comes from a GSLT program of adjacent swaps over any
alphabet, realized by two physical rings per move with the boundary shift
accounted for. It does not require enumerating the finite word state space.
Longer literal tubes therefore admit a strict vertex-count decrease and
colouring reconstruction in both directions. The GSLT replacement retains
the complete colouring witnesses of both serial exterior pieces. This is
support preservation, not equality of counting matrices. The same literal
tubes have a proved oriented boundary-face return, independent of length,
and open Euler mass four. The exact face-sewing law counts internal cycles
created at every seam. The actual interior multigraph of every tube of
circumference at least two is connected and bridgeless. Replacing one tube
length by another preserves the conjunction of connectedness and
bridge-freedom in every fixed closed sewing context. This follows from a
general replacement criterion: only realized cut states of cost at most one
affect that conjunction, and nonempty connected bridgeless pieces have the
same two constant states there. The standard-port face return also preserves
the closed Euler characteristic and all exterior cofaciality. Literal tube
vertices are cubic and rotation-cyclic; these exterior conditions are
recovered from the original closed map. Consequently replacing a long tube
by the explicit shorter tube gives a strict vertex decrease in the actual
connected bridgeless spherical cubic map class. Tait-colourability is
equivalent in both closed composites, and explicit colouring reconstruction
keeps every exterior dart's edge colour. This is a full reduction for the
literal tube family, not a supply theorem for general linked bands or a
uniform bound on minimal counterexamples.
For circumference five, the earlier kernel-checked finite certificate now
improves the literal normal form from forty rings to four. The equality of
four- and five-ring support propagates to every longer tube. Reduction keeps
the same physical source class and reconstructs every exterior edge colour.
The GSLT boundary-certificate theorem composes these local replacements along
arbitrary finite routes; nonempty chains have literal serial realizations
whose colouring witnesses are equivalent to the route witnesses. Arbitrary
tests of the outer boundary are preserved. This independent family theorem
does not remove a certificate from the classical unavoidable catalogue.
An induced cyclic row in an actual cubic graph now constructs the complete
zigzag-slab dart embedding from its adjacency and cut attachment conditions.
Cubicity supplies the unique unused edge at each row vertex; chordlessness
makes it leave the row. The resulting boundary maps exhaust both cuts.
Colourings of the enlarged region are equivalent to compatible pairs of an
inner colouring and a ring colouring, with both given witnesses retained.
This is an incidence and colouring theorem, independent of vertex rotation.
It does not establish that extracted contours are induced and alternating,
or identify the face permutation of an arbitrary annulus with a literal tube.
For a chordless cycle oriented along a connected facial region with connected
complement, alternating retained degrees now derive all attachment conditions
and the ambient ring rotation. The interior is the original vertices whose
incident faces are all selected; the interior plus the row is exactly the
vertices touched by the selected faces. Opening the graph on the row gives
an equivalence with literal ring darts that conjugates the complete open-face
permutation. This proves geometric recognition for that boundary pattern.
For an alternating facial cycle, chordlessness is now derived if every port
face has length five or six. Three-step facial arcs propagate any hypothetical
chord to a shorter cyclic gap, ending at a fixed edge reversal or a three-step
face. This constructs the induced cycle and consumes the same physical slab
and open-face transport results. More generally, when port faces have length
at least five, a chord forces a port face of length at least seven.
For consecutive oriented slabs, the actual boundary bijections construct the
seam permutation. Three-step facial arcs on its two sides show that hexagonal
seam faces force that permutation to be a cyclic translation. Accumulating
these translations aligns an arbitrarily long chain and gives the exact
iterated ring support, with genuine side-colouring witnesses. The existing
strict shore splice therefore excludes excessively long such chains in a
graph-backed minimal counterexample without an assumed common port labelling.
The newer whole-strip assembly identifies every recognized nonempty chain
with the literal tube, preserving all original vertices, darts, edge mates,
vertex rotations and ordered end ports. Cutting out those exact vertices and
sewing the tube into its actual exterior is an exact relabelling. Consequently
a five-port strip with at least five rows reduces to four, removing ten
vertices per deleted row inside the same bridgeless spherical cubic class.
Reconstruction retains every exterior edge colour. The minimal-counterexample
bound improves from the coarse 446403 to four rows, without extra connected-
shore hypotheses. Optimality of four is not asserted. The facial-row adapter
consumes this bound directly. Alternation, supply of consecutive recognized
rows, interface-width control and general strict-reduction coverage remain open.
One successor row can now be constructed from the original hexagonal collar.
Edge reversal and rotation determine its candidate vertices and darts. If the
candidate vertices are distinct and the new output-port faces have length five
or six, the construction derives the complete new slab, its orientation and
its exact two-ended colouring semantics. Conversely, any oriented successor
has those candidate vertices up to its actual seam bijection. Distinctness is
therefore the exact successor criterion under the stated face hypotheses.
Candidate distinctness is now derived from cubic rotation and the original
hexagonal seam faces. Complete old boundaries exclude candidate returns;
mixed identifications propagate by cyclic reflection to an impossible fixed
point of edge reversal. Thus hexagonal collars cannot stop by identifying
vertices, at any positive width. In finite pentagon/hexagon maps, growth reaches
an actual pentagonal seam within the coarse bound given by the vertex count.
A least counterexample reaches one within three extensions of a supplied
five-port row; otherwise the construction supplies a reducible five-row tube.
No reduction at the pentagonal stop is asserted. Initial alternating-row
supply, changing widths and non-fullerene maps remain coverage obligations.
AlternatingCycleRecognition now constructs a complete oriented row from a
simple cycle with alternating local turns, at every width k ≥ 2. Spherical
separation supplies both connected facial shores; short port faces exclude
chords. The interior, retained degree pattern and both complete ordered
interfaces are derived. Exact joint colouring support and the original darts
are preserved. This recognition feeds finite pentagonal termination and, at
width five, the three-extension bound from physical reduction. A suitable
simple alternating cycle still has to be supplied. Independent dart/phase
orbit tests find wider rows in the formerly empty five-port Goldberg examples,
but also nonsimple orbits in capped strips. Neither universal simplicity nor
universal row supply is inferred from those finite tests.
AlternatingWalkLobes now supplies a simple contiguous cycle from every
alternating dart/phase trajectory in a finite cubic graph. Its length lies
between three and the ambient vertex count; its actual darts and every
internal transition are retained. In a bridgeless spherical cubic graph,
the cycle constructs exact facial separation with both shores connected.
Only its closing transition is unrestricted. This is not yet a tube row
or a reducible patch. Independent replay of 137 fullerene rotations finds
30 with no simple complete alternating orbit. A 30-vertex witness has orbit
lengths 68, 22, 68, 22 and no cyclic edge cut of size at most four; an explicit
Tait colouring is retained. The next geometric contract must account for
the closing transition rather than assume a simple complete orbit exists.
CycleSeamTransfer proves the colouring part for literal cycle tangles of
every length at least three. Contracting distinct nonzero first ports adds
their Klein colours and erases one internal edge. Retaining the incoming
seam colour s makes reconstruction exact: s must differ from the first
old port colour. Actual tangle witnesses are extracted and rebuilt, and
any predicate on this marked seam can be retained. A four-cycle with
alternating red/blue ports has no colouring although its contracted triangle
does, so unmarked contraction alone is insufficient. Both assertions are
kernel checked. The C30 lobe's colouring restriction is an independent program
consumer. A formal adapter preserving that lobe's two-sided port placement,
an exterior operation, strict map reduction and coverage remain open.
Every connected face region with connected complement now constructs a
literal plane patch on its retained edges. The outer facial orbit is exactly
the complete original mixed-vertex contour; its inner faces correspond
bijectively to the selected original faces, preserving dart lengths. This
applies directly to the deep distance regions. Their signed curvature is
`6 - n₂ + n₃` for the actual boundary degree counts. Alternation requires
curvature six, hence six pentagons when the selected faces have length five
or six. A shell of hexagonal faces preserves this degree imbalance; neither
equal boundary lengths nor alternating boundary codes follow from that law.
The actual facial dual has no cut vertex. A finite connected-bipartition
argument now refines every nested pair of connected facial sides with
connected complements into single-face additions. These are authored GSLT
routes, of exactly the face-count difference, and every state realizes as
the literal plane patch. Every source map supplies a sweep from one face to
all but its designated outer face; the last state retains all original
vertices and edges. Nested distance contours admit the same refinement.
Each event toggles exactly its face edges in the complete contour. Its
boundary length changes by face length minus twice the attachment-edge
count, while its degree imbalance changes by face length minus six. These
events have nonempty proper attachment arcs in the original face order and
in the old boundary order, with pointwise agreement under the dart inclusion.
The new edges form one arc of the actual new boundary. The surviving darts
exhaust its complement, their successor steps are unchanged away from the
junctions, and the exact entry and rejoining equations identify the ordered
splice. The exposed arc now gives a simple path on the original edge and
vertex identifiers, including its distinct terminal vertex. It meets the
old patch exactly at its two ends. Gluing specified old and new colouring
witnesses is proper exactly when the old colouring is proper, consecutive
new-edge colours differ, and each end colour avoids the corresponding old
endpoint profile. Every extension is recovered, and successful local choices
construct extensions retaining all old colours. The existing finite support
fork law specializes to compatibility tests at just these two endpoints.
These statements derive the path from every facial event. They do not assert
that a whole source route has compatible witnesses. Each attachment endpoint
has exactly two old incident edges and hence a unique missing colour in every
proper old colouring. The exact extension classification is now proved:
one new edge requires equal missing colours, two require different missing
colours, and three or more always extend the fixed old colouring. All old
edge colours are preserved. The actual attachment degree word is now proved
to be `2, 3, ..., 3, 2`; the new arc has word `3, 2, ..., 2, 3`. Excluding
a run of r degree-three vertices bounds attachment length by r. A new face
of length at least r+3 therefore extends every proper old colouring, and
the geometric event toward any larger connected facial target is constructed.
In particular a blocked pentagonal step requires a run of two degree-three
vertices; a blocked hexagonal step requires three. These are necessary
conditions, not converses. Every step exposing at least three edges creates
consecutive degree-two vertices and hence loses alternation. For a hexagonal
step from an alternating contour, curvature six forces consecutive threes
as well. Neither alternation nor exclusion of consecutive threes propagates
through all single-face steps. Compatible groups of steps or control of the
resulting boundary runs remain open, along with general reduction supply.
A two-event family now admits jointly chosen colourings: the first face
exposes at least four edges; the second exposes two and joins an original
vertex to a new vertex adjacent to the original patch. Actual incidences
construct the endpoint positions and both colouring witnesses. Cubicity
keeps the original contact's profile unchanged; freedom near an end of
the first path makes the other missing colour different. The original
patch's colouring is preserved throughout. A fifteen-edge incidence
example proves that a valid first choice can fail even though the pair
has a successful joint choice. General availability and repeated progress
for such pairs and the remaining short-step contacts remain open.
The order of two actual additions can also be exchanged. If k newly exposed
edges are common to the two faces, more than k attachment edges of the second
face and more than k exposed edges of the first construct both connected
shores of the exchanged middle region. The new exposure counts are n₂+k
and n₁-k. When both are at least three, every original colouring extends
through the exchanged order; restriction of the final witness also supplies
jointly chosen witnesses for the original order. A four/two pair sharing one
new edge is a special case. No general supply of such pairs is asserted.
An exact budget limits this mechanism: summing 3-n over a complete facial
sweep gives the initial face length, independently of the ordering. Each
one- or two-edge addition contributes at most two; longer additions contribute
zero or less. Thus a sweep starting from a pentagon necessarily has at least
three short additions. Reordering can move the constraints but cannot remove
all of them. Compatible choices for the unavoidable short steps remain part
of the universal construction problem.
The three-edge/two-edge adjacent-contact pair now has an exact transfer
criterion. Its three old contact vertices u,t,w are constructed or identified
from incidence and proved distinct. If their original missing colours are
r,s,q, where u is the old neighbour of the new branching vertex and t is
the other first-path endpoint, jointly chosen extensions exist exactly when
q=r or q differs from s. The only forbidden pattern is q=s different from r.
The geometric path, its orientation, its other endpoint and all missing
colours are derived; no successful-transfer supplier is assumed in this
source theorem. The pair has signed deficit one, so it addresses a short
constraint that cannot be replaced by two unconditional long steps.
An eighteen-edge incidence witness has the forbidden missing pattern and
no extension preserving its original colouring, even though a first-step
extension exists. Revising four original edge colours supplies a proper
colouring of the whole pair. Those four edges are now certified as one
complete two-colour component of the original patch, and its actual switch
produces the stated revision. This example checks incidences, components
and colourings, not a spherical rotation-system instance.
For every pair with the stated adjacent-contact geometry, every proper
original colouring now admits a physical Kempe history of length at most
one followed by jointly compatible proper extensions through both events.
The proof derives a generic endpoint bound: a two-colour component of an
ordinary incidence graph can touch at most two distinct vertices missing
one of its selected colours. Switching the component through w therefore
repairs the only forbidden triple. The pair preserves existence of a
colouring in both directions. The old witness may change along a component
of unbounded length; no bound on that length or on contour width is implied.
General occurrence of suitable groups and repeated progress remain open.
A matching of fresh edges admits a strict extension exactly when each
fresh edge has a colour absent at all its old endpoint profiles. This
constructs the enlarged witness on the same original edge identifiers.
For distinct unique endpoint requests, only their own colour transposition
can equalize them in one switch, and a saturated chain joining the contacts
prevents that repair. A concrete thirty-vertex cubic sphere has a prescribed
old colouring requiring exactly three physical switches before a matching
of two missing edges can be restored. All seventeen actual faces have five
or six boundary edges; the omitted edges are disjoint and cofacial on a
hexagon. The old edges are exactly a selected facial region with connected
complement. Every possible first switch is covered by five actual component
chains and the unchanged case; each resulting state still has a blocked
endpoint pair after every single further switch. An explicit three-step
GSLT history and full forty-five-edge colouring attain the lower bound.
This refutes a uniform two-switch repair claim in this geometry. It does
not supply a bound for all matching caps, a proof of all normal-form cut
conditions, or a successful colouring history for every source construction.
The final three-edge facial addition before a two-edge cap now identifies
the old patch exactly with deletion of its two adjacent internal vertices.
Cubic facial incidence makes the two missing edges disjoint and the four
external ports distinct. The actual event and edge counts supply the ordered
deletion data; no boundary arc or colouring success is an additional supplier.
The original three-colour assignment transports to the existing four-port
restoration theory. It extends to the whole ambient graph, preserving every
old edge colour, exactly when its request word does not have equal colours
on both same-vertex port pairs. Every restored boundary edge must carry its
old port's requested colour. Thus looking back one construction step exposes
the existing adjacent-pair compatibility problem, rather than a new mixing
mechanism. Universal availability of an accepted old witness remains open.
The terminal geometry is now supplied around any adjacent pair of a
vertex-minimal Tait counterexample. Selecting precisely the original faces
avoiding the pair retains exactly the induced deletion's edges. Both facial
shores are connected. Adding a face through the central edge is an actual
event exposing three original edges and leaving two missing; a complete
uncoloured prefix starts from a single original face. The construction uses
normal-form face intersections, dual triangles, and disk Euler counts. It
assumes neither a terminal patch nor a boundary ordering. It supplies no
accepted old colouring, successful coloured route, or finite generating base.
An actual adjacent-pair deletion in a thirty-vertex bridgeless cubic sphere
now has a proper starting colouring from which no finite physical Kempe
history extends back to the ambient map. Six representatives and palette
permutations give a switch-closed family. Its two ports at one deleted
vertex always request the same colour. The same rotation has an explicit
full colouring, girth five, pentagonal or hexagonal faces, and connected
facial shores before and after the three-edge terminal addition. Thus
girth five and this terminal geometry do not make every starting choice
repairable. The replay tool additionally checks dual connectivity after
up to four face deletions and small cyclic cuts; those extra checks are
diagnostics and are not asserted as Lean normal-form theorems here.
Physical Kempe switches now act on the same original edge assignments and
transport each vertex profile exactly. Every failed facial extension supplies
a colour pair and a component through its first endpoint; the chosen switch
repairs it exactly when the component avoids its second endpoint. Otherwise
there is an actual two-colour walk through retained edges joining the ends.
Switches contacting both ends, or neither, preserve the extension test.
An explicit rectangular-shore colouring on triangular-prism incidence admits
no extension after any single component switch, but an explicit two-switch
sequence does extend. This control is proved in incidence semantics; its
spherical facial-event adapter is not formalized here. The source-map repair
criterion is independent of this control.
A second, twelve-vertex witness rules out arbitrary finite Kempe repair of a
prescribed old colouring. A finite family of retained assignments is closed
under every actual component switch, certified by connected saturated chains.
Induction over the existing GSLT route type then proves that no reachable
assignment extends to any strict superset of the old edges. Both missing
ambient edges remain blocked, so changing the next addition does not help.
The actual connected bridgeless spherical cubic rotation, its eight face
cycles, and connected sides of the old and enlarged regions are kernel checked.
Those literal face unions retain exactly the edges used by the obstruction.
A different assignment properly colours the entire ambient map. This is a
failure of universal repair from arbitrary old choices, not of existential
compatible construction. The witness contains triangles and squares and
does not refute a repair theorem restricted to the stronger normal form.
Construction with earlier choices revised, or strict replacement and
reconstruction, still needs a geometric progress argument.
A literal one-face rollback now escapes that same trapped family: two actual
component switches on the smaller patch permit reconstruction of the full
map. All rollback and reconstruction regions have connected complementary
facial shores. Five specified old edges retain their colours throughout.
The first smaller switch has no proper return to the old patch; the second
restores reconstructibility. Passing through that extra smaller state is
permitted by the rollback.
A generic theorem proves uniqueness of reconstruction across an exposed
path of at most two edges when each old endpoint profile omits one colour.
It applies to the rolled-back path. Nevertheless no old Kempe history ends
at any colouring restricting to the final smaller witness. Thus uniqueness
of colouring reconstruction does not imply lifting of recolouring histories.
This certificate supplies one successful revised construction; universal
availability of a successful rollback and a general bound remain unproved.
For a removed path of one or two edges, a smaller physical switch whose
endpoints both reconstruct now lifts to a finite old Kempe history. Forced
endpoint colours make the change a pointwise partial transposition; a
generic theorem for finite graphs decomposes every proper such change into
actual components. Consequently every GSLT route within the image of
reconstruction gives old reachability. The actual spherical face theorem
supplies all endpoint-profile hypotheses. Applied to the trapped witness,
there is no route between its initial and final smaller colourings that
stays in that image. Thus leaving reconstructibility is necessary for
every escape between those endpoints, not only the exhibited two switches.
This identifies a necessary feature of repair without supplying such an
escape for arbitrary maps.
For a facial rollback deleting at least three exposed edges, every smaller
Kempe history lifts to any specified proper old reconstruction, including
its colours on all restored edges. The proof first lifts across vertices
of degree at most two in an arbitrary finite graph. A relative elimination
theorem then iterates this over the deleted set. The literal incidence graph
of a long exposed path supplies such an elimination: internal edges have
degree at most two, and after their removal the two end edges are separated
and have at most two retained neighbours each. The spherical event supplies
the path and endpoint degree bounds. Consequently an actual one-face rollback
which escapes an old Kempe class must delete one or two edges. Combining
this with short-path lifting proves that every such escape must leave the
reconstruction image. These are necessary conditions; neither the existence
of a useful short rollback nor progress of repeated rollback is established.
This build root does not establish either decomposition supply or finite-base
verification, and is deliberately separate from `FourColorLane`.
-/
