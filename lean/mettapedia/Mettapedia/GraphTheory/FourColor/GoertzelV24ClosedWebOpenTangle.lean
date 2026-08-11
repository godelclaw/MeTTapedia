import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceAmbientFaceCount

/-!
# The Cell-3 carrier is an open tangle

The source's closed-web-at-good-word cell is an annular tangle: its named
inner and outer interface vertices have degree one.  It must therefore not be
identified with the closed cubic graph used by the global minimal-counterexample
normal form.  Any later use of closed ambient normality has to pass through an
explicit cap-deletion or closure construction.

This small guard theorem makes that type distinction kernel-visible, so a
vacuous closed-cubic-minimal hypothesis cannot silently enter the Cell-3
splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24FaceDualConnectedness
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24HexFaceRungType
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SpliceUnification
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebOpenTangleEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

/-- A Cell-3 open tangle cannot itself carry the closed cubic
minimal-counterexample structure: its first inner stub has degree one, while
that structure makes every vertex cubic. -/
theorem graphBackedVertexMinimalTaitCounterexample_elim
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) : False := by
  have hregular : G.IsRegularOfDegree 3 :=
    web.annular.cellulation.rotation.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic
  have hone : G.degree (data.innerStub 0) = 1 := by
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
      (G := G)]
    exact web.boundary_wellFormed.inner_stub_degree_one 0
  have hthree : G.degree (data.innerStub 0) = 3 :=
    hregular (data.innerStub 0)
  omega

/-- A dart of an annular-interior face cannot be based at an interface stub.
The degree-one edge of either stub is entirely on its named hole face, while
this dart lies on neither hole. -/
theorem vertOf_mem_interiorVertices_of_dartOrbitFace_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {dart : web.annular.RS.D}
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    web.annular.RS.vertOf dart ∈ data.interiorVertices := by
  rw [interiorVertices]
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [FramedAnnularCellulation.interiorFaces] at hface
  have hnotHole := (Finset.mem_sdiff.mp hface).2
  intro hboundary
  rw [boundaryStubVertices, Finset.mem_union] at hboundary
  have hincident : web.annular.RS.edgeOf dart ∈
      incidentEdgeFinset G (web.annular.RS.vertOf dart) := by
    change (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet) ∈
      incidentEdgeFinset G dart.fst
    simp [incidentEdgeFinset, SimpleGraph.Dart.edge]
  rcases hboundary with hinner | houter
  · rcases (mem_innerStubVertices_iff data _).1 hinner with ⟨inner, hstub⟩
    have hincidentInner : web.annular.RS.edgeOf dart ∈
        incidentEdgeFinset G (data.innerStub inner) := by
      simpa [hstub] using hincident
    rw [data.innerStub_incidentEdgeFinset_eq_singleton
      web.boundary_wellFormed inner] at hincidentInner
    have hedge : web.annular.RS.edgeOf dart = data.innerBoundaryEdge inner :=
      Finset.mem_singleton.mp hincidentInner
    have hdart : dart ∈ web.annular.RS.dartsOn (data.innerBoundaryEdge inner) :=
      web.annular.RS.mem_dartsOn.2 hedge
    have hhole := web.annular.innerBoundaryEdgeDarts_on_innerHole
      inner dart hdart
    apply hnotHole
    rw [hhole]
    simp [FramedAnnularCellulation.holeFaces]
  · rcases (mem_outerStubVertices_iff data _).1 houter with ⟨outer, hstub⟩
    have hincidentOuter : web.annular.RS.edgeOf dart ∈
        incidentEdgeFinset G (data.outerStub outer) := by
      simpa [hstub] using hincident
    rw [data.outerStub_incidentEdgeFinset_eq_singleton
      web.boundary_wellFormed outer] at hincidentOuter
    have hedge : web.annular.RS.edgeOf dart = data.outerBoundaryEdge outer :=
      Finset.mem_singleton.mp hincidentOuter
    have hdart : dart ∈ web.annular.RS.dartsOn (data.outerBoundaryEdge outer) :=
      web.annular.RS.mem_dartsOn.2 hedge
    have hhole := web.annular.outerBoundaryEdgeDarts_on_outerHole
      outer dart hdart
    apply hnotHole
    rw [hhole]
    simp [FramedAnnularCellulation.holeFaces]

/-- The source tangle is locally cubic at every dart of an annular-interior
face.  This is the replacement for applying a global closed-cubic hypothesis
to the open Cell-3 carrier. -/
theorem incidentEdgeFinset_card_eq_three_of_dartOrbitFace_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {dart : web.annular.RS.D}
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    (incidentEdgeFinset G (web.annular.RS.vertOf dart)).card = 3 := by
  exact interior_incidentEdgeFinset_card_eq_three data web.boundary_wellFormed
    (web.vertOf_mem_interiorVertices_of_dartOrbitFace_mem_interiorFaces hface)

/-- The same local cubic fact in the rotation-system form used by corridor
corner lemmas. -/
theorem dartsAt_card_eq_three_of_dartOrbitFace_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {dart : web.annular.RS.D}
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    (web.annular.RS.dartsAt (web.annular.RS.vertOf dart)).card = 3 := by
  change ({candidate : G.Dart | candidate.fst = dart.fst} : Finset G.Dart).card = 3
  rw [G.dart_fst_fiber_card_eq_degree dart.fst]
  rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := G)]
  exact web.incidentEdgeFinset_card_eq_three_of_dartOrbitFace_mem_interiorFaces
    hface

/-- The annular cellulation already carries the cyclic local rotation needed
by the corridor corner calculus. -/
theorem vertexRotationCyclic
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :
    VertexRotationCyclic web.annular.RS := by
  exact hasCyclicVertexRotations_implies_vertexRotationCyclic G
    web.annular.cellulation.rotation
    web.annular.cellulation.vertexRotation_cyclic

/-- An annular-interior face has the simple edge boundary certified by the
Cell-3 geometry.  This is the local replacement for a global two-sided-face
hypothesis, which would be false at the named degree-one holes. -/
theorem orbitFaceBoundary_card_eq_orbitFaceDarts_card_of_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    (orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS dart)).card =
        (orbitFaceDarts web.annular.RS
          (dartOrbitFace web.annular.RS dart)).card := by
  simpa [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.faceLength] using
    web.geometry.internalBoundarySimple
      (dartOrbitFace web.annular.RS dart) hface

/-- A dart incident to an annular-interior face has a genuinely different
face on its opposite side.  The Cell-3 tangle need not be globally two-sided:
the degree-one stub edges deliberately run twice around a named hole.  What
the source corridor uses is this local fact, obtained from the certified
simple boundary of each interior face. -/
theorem dartOrbitFace_ne_alpha_of_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    dartOrbitFace web.annular.RS dart ≠
      dartOrbitFace web.annular.RS (web.annular.RS.alpha dart) := by
  intro hsame
  have hsimple :=
    web.orbitFaceBoundary_card_eq_orbitFaceDarts_card_of_mem_interiorFaces
      dart hface
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS dart)) := by
    apply Finset.card_image_iff.mp
    exact hsimple
  have hdart : dart ∈ orbitFaceDarts web.annular.RS
      (dartOrbitFace web.annular.RS dart) :=
    (mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS dart) dart).2 rfl
  have halpha : web.annular.RS.alpha dart ∈ orbitFaceDarts web.annular.RS
      (dartOrbitFace web.annular.RS dart) :=
    (mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS dart)
      (web.annular.RS.alpha dart)).2 hsame.symm
  have heq := hinjective hdart halpha
    (web.annular.RS.edge_alpha dart).symm
  exact web.annular.RS.alpha_fixfree dart heq.symm

/-- The cyclic edge positions of an annular-interior face are distinct.  The
corridor may use this local fact without treating the open Cell-3 tangle as a
globally two-sided spherical map. -/
theorem faceCycleEdge_injective_of_dartOrbitFace_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (root : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS root ∈
      web.annular.cellulation.interiorFaces) :
    Function.Injective (faceCycleEdge web.annular.RS root) :=
  faceCycleEdge_injective_of_boundarySimple web.annular.RS root
    (web.orbitFaceBoundary_card_eq_orbitFaceDarts_card_of_mem_interiorFaces
      root hface)

/-- A selected edge on an annular-interior face has a unique position in that
face's real cyclic boundary. -/
theorem existsUnique_faceCycleEdge_eq_of_dartOrbitFace_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (root : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS root ∈
      web.annular.cellulation.interiorFaces)
    (edge : G.edgeSet)
    (hedge : edge ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS root)) :
    ∃! position : Fin (web.annular.RS.faceOrbit root).card,
      faceCycleEdge web.annular.RS root position = edge :=
  existsUnique_faceCycleEdge_eq_of_boundarySimple web.annular.RS root
    (web.orbitFaceBoundary_card_eq_orbitFaceDarts_card_of_mem_interiorFaces
      root hface) edge hedge

/-- Addendum XXVII(iii)'s statement that a named hole lies outside the pumped
region: every occurrence on that facial boundary remains on the retained
side.  It is deliberately stronger than merely retaining the five named stub
edges, because it lets the whole hole face survive the splice unchanged. -/
def HoleFaceKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS) : Prop :=
  ∀ dart : web.annular.RS.D,
    dartOrbitFace web.annular.RS dart = face →
      splice.keep (web.annular.RS.vertOf dart)

/-- A source face wholly outside the pumped region is an ambient retained
face in the generic splice calculus. -/
noncomputable def ambientRetainedFaceOrbit_of_holeFaceKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS)
    (hkept : HoleFaceKept splice face) :
    AmbientRetainedFaceOrbit web.annular.RS splice.keep :=
  ⟨face, by
    rintro ⟨dart, hdeleted, hdartFace⟩
    exact hdeleted (hkept dart hdartFace)⟩

/-- The protected source face has a canonical seam-free face in the shortened
rotation system.  This transports the actual facial cycle, not merely the
named degree-one stubs on it. -/
noncomputable def outputFaceOrbit_of_holeFaceKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS)
    (hkept : HoleFaceKept splice face) :
    SpliceNonSeamOrbit web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
      splice.rightCrosses splice.leftInjective splice.rightInjective
      splice.cover splice.disjoint splice.outer_kept :=
  ambientRetainedFaceOrbitToSplice web.annular.RS splice.keep
    splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
    splice.rightCrosses splice.leftInjective splice.rightInjective
    splice.cover splice.disjoint splice.outer_kept
    (ambientRetainedFaceOrbit_of_holeFaceKept splice face hkept)

/-- The two protected source holes remain distinct output faces.  The splice
therefore preserves the annular two-hole interface at the face-orbit level,
rather than merely retaining its boundary stubs. -/
theorem outputInnerHole_ne_outputOuterHole
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    (outputFaceOrbit_of_holeFaceKept splice web.annular.cellulation.innerHole
      hinner).1 ≠
      (outputFaceOrbit_of_holeFaceKept splice web.annular.cellulation.outerHole
        houter).1 := by
  intro hfaces
  have htransport :
      ambientRetainedFaceOrbit_of_holeFaceKept splice
        web.annular.cellulation.innerHole hinner =
      ambientRetainedFaceOrbit_of_holeFaceKept splice
        web.annular.cellulation.outerHole houter := by
    apply ambientRetainedFaceOrbitToSplice_injective web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
      splice.rightCrosses splice.leftInjective splice.rightInjective
      splice.cover splice.disjoint splice.outer_kept
    exact Subtype.ext hfaces
  apply web.annular.cellulation.holes_ne
  exact congrArg Subtype.val htransport

/-- Full preservation of the inner hole entails the earlier five-stub
interface condition used to preserve the good word. -/
theorem innerBoundaryKept_of_innerHoleFaceKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hkept : HoleFaceKept splice web.annular.cellulation.innerHole) :
    ProtectedInnerInterface.InnerBoundaryKept splice := by
  intro port dart hdart
  exact hkept dart
    (web.annular.innerBoundaryEdgeDarts_on_innerHole port dart hdart)

/-- Full preservation of the outer hole entails the corresponding outer-stub
condition. -/
theorem outerBoundaryKept_of_outerHoleFaceKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hkept : HoleFaceKept splice web.annular.cellulation.outerHole) :
    ProtectedInnerInterface.OuterBoundaryKept splice := by
  intro port dart hdart
  exact hkept dart
    (web.annular.outerBoundaryEdgeDarts_on_outerHole port dart hdart)

namespace ProtectedInnerInterface

attribute [local instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

/-- The source-oriented dart at an inner stub determines its retained output
vertex whenever the source layer stays outside the inner hole. -/
noncomputable def retainedInnerStub
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hkept : InnerBoundaryKept splice) (port : Fin 5) :
    RetainedVertex splice.keep :=
  ⟨data.innerStub port, by
    rw [← innerBoundaryDart_fst data web.boundary_wellFormed port]
    exact hkept port
      (innerBoundaryDart data web.boundary_wellFormed port)
      (innerBoundaryDart_mem_dartsOn web.annular web.boundary_wellFormed port)⟩

/-- A splice whose pumped region avoids the inner hole retains each named
inner stub with its exact degree-one local rotation.  This is a concrete
piece of the source's hole-gathering checklist, not a closed-cubic output
claim. -/
theorem output_dartsAt_card_eq_one_of_innerBoundaryKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hkept : InnerBoundaryKept splice) (port : Fin 5) :
    (splice.output.dartsAt (retainedInnerStub splice hkept port)).card = 1 := by
  change
    ((orderedCutRetainedVertexRotationSystem web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
      splice.rightCrosses splice.leftInjective splice.rightInjective
      splice.cover splice.disjoint splice.outer_kept splice.seamEndpoints).dartsAt
        (retainedInnerStub splice hkept port)).card = 1
  rw [orderedCutRetainedVertexRotationSystem_dartsAt_card web.annular.RS
    splice.keep splice.left.crossingEdge splice.right.crossingEdge
    splice.leftCrosses splice.rightCrosses splice.leftInjective
    splice.rightInjective splice.cover splice.disjoint splice.outer_kept
    splice.seamEndpoints (retainedInnerStub splice hkept port)]
  change ({dart : G.Dart | dart.fst = data.innerStub port} : Finset G.Dart).card = 1
  rw [G.dart_fst_fiber_card_eq_degree (data.innerStub port)]
  rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := G)]
  exact web.boundary_wellFormed.inner_stub_degree_one port

/-- The source-oriented dart at an outer stub determines its retained output
vertex whenever the source layer stays outside the outer hole. -/
noncomputable def retainedOuterStub
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hkept : OuterBoundaryKept splice) (port : Fin 5) :
    RetainedVertex splice.keep :=
  ⟨data.outerStub port, by
    rw [← outerBoundaryDart_fst data web.boundary_wellFormed port]
    exact hkept port
      (outerBoundaryDart data web.boundary_wellFormed port)
      (outerBoundaryDart_mem_dartsOn web.annular web.boundary_wellFormed port)⟩

/-- A splice whose pumped region avoids the outer hole retains each named
outer stub with its exact degree-one local rotation. -/
theorem output_dartsAt_card_eq_one_of_outerBoundaryKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hkept : OuterBoundaryKept splice) (port : Fin 5) :
    (splice.output.dartsAt (retainedOuterStub splice hkept port)).card = 1 := by
  change
    ((orderedCutRetainedVertexRotationSystem web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
      splice.rightCrosses splice.leftInjective splice.rightInjective
      splice.cover splice.disjoint splice.outer_kept splice.seamEndpoints).dartsAt
        (retainedOuterStub splice hkept port)).card = 1
  rw [orderedCutRetainedVertexRotationSystem_dartsAt_card web.annular.RS
    splice.keep splice.left.crossingEdge splice.right.crossingEdge
    splice.leftCrosses splice.rightCrosses splice.leftInjective
    splice.rightInjective splice.cover splice.disjoint splice.outer_kept
    splice.seamEndpoints (retainedOuterStub splice hkept port)]
  change ({dart : G.Dart | dart.fst = data.outerStub port} : Finset G.Dart).card = 1
  rw [G.dart_fst_fiber_card_eq_degree (data.outerStub port)]
  rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := G)]
  exact web.boundary_wellFormed.outer_stub_degree_one port

end ProtectedInnerInterface

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
