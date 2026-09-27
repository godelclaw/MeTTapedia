import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkChecks
import Mettapedia.GraphTheory.FourColor.SphericalProtectedLinkedBand
import Mettapedia.GraphTheory.FourColor.FaceRegionCurvature
import Mettapedia.GraphTheory.FourColor.FaceRegionSweep
import Mettapedia.GraphTheory.FourColor.FaceBoundaryJunctions
import Mettapedia.GraphTheory.FourColor.FaceColourTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCountGrowth
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonTubeSaturation
import Mettapedia.GraphTheory.FourColor.OddCappedTubeSaturation
import Mettapedia.GraphTheory.FourColor.ZigzagRingTwoColour
import Mettapedia.GraphTheory.FourColor.ZigzagTubeCompression
import Mettapedia.GraphTheory.FourColor.ZigzagRingGeometry
import Mettapedia.GraphTheory.FourColor.ZigzagTubeStructural
import Mettapedia.GraphTheory.FourColor.ZigzagTubeReplacement
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

/-!
# Supplemental research checkpoint

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
existence of compatible witnesses on those source routes remains unproved.
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
stabilizes after the explicit bound `2 * 4^k + k`: full-colour words are
classified by multiplicities, and missing-colour words by cyclic rotation.
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
that every old colouring extends, or that a whole source route has compatible
witnesses. No bounded width or general reduction supply follows from them.
This build root does not establish either decomposition supply or finite-base
verification, and is deliberately separate from `FourColorLane`.
-/
