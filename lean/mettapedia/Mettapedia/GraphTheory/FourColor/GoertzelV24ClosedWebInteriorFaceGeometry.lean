import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

/-!
# Local interior-face geometry for the Cell-3 open tangle

The Cell-3 carrier has degree-one interface stubs, so global cubicity and
global face two-sidedness are both false.  The source corridor, however,
uses only annular-interior faces and their immediate neighbours.  This file
records the elementary local replacements: simple facial boundaries, cyclic
vertex rotations, and degree three at every vertex reached through an
interior face.  Keeping them in this light module lets source-layer formation
use the real open tangle without importing the closed-cubic collar stack.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexFaceRungType
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace InteriorFace

/-- A dart on an annular-interior face cannot be based at one of the two
degree-one interfaces. -/
theorem vertOf_mem_interiorVertices
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

/-- The source tangle is locally cubic at a dart of an annular-interior
face.  This is deliberately a local statement rather than a false global
cubicity assertion. -/
theorem dartsAt_card_eq_three
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {dart : web.annular.RS.D}
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    (web.annular.RS.dartsAt (web.annular.RS.vertOf dart)).card = 3 := by
  change ({candidate : G.Dart | candidate.fst = dart.fst} : Finset G.Dart).card = 3
  rw [G.dart_fst_fiber_card_eq_degree dart.fst]
  rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := G)]
  exact interior_incidentEdgeFinset_card_eq_three data web.boundary_wellFormed
    (vertOf_mem_interiorVertices web hface)

/-- The cellulation itself supplies cyclic vertex rotations everywhere. -/
theorem vertexRotationCyclic
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :
    VertexRotationCyclic web.annular.RS := by
  exact hasCyclicVertexRotations_implies_vertexRotationCyclic G
    web.annular.cellulation.rotation
    web.annular.cellulation.vertexRotation_cyclic

/-- An annular-interior face has the simple edge boundary certified by the
Cell-3 geometry. -/
theorem boundary_card_eq_darts_card
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    (orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS dart)).card =
        (orbitFaceDarts web.annular.RS
          (dartOrbitFace web.annular.RS dart)).card := by
  simpa [FramedAnnularCellulation.faceLength] using
    web.geometry.internalBoundarySimple
      (dartOrbitFace web.annular.RS dart) hface

/-- The opposite dart of a boundary dart of an interior face lies on a
different quotient face. -/
theorem dartOrbitFace_ne_alpha
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    dartOrbitFace web.annular.RS dart ≠
      dartOrbitFace web.annular.RS (web.annular.RS.alpha dart) := by
  intro hsame
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS dart)) := by
    apply Finset.card_image_iff.mp
    exact boundary_card_eq_darts_card web dart hface
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

/-- Every edge met by an annular-interior face is an honest interior edge of
the facial incidence model.  The open tangle need not be globally two-sided:
the simple source face and the opposite dart already exhibit the two distinct
incident faces, while the rotation-system incidence theorem rules out a
third. -/
theorem edge_mem_interiorEdgeSupport
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    web.annular.RS.edgeOf dart ∈ interiorEdgeSupport
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) := by
  apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).2
  refine ⟨Finset.mem_biUnion.2 ⟨dartOrbitFace web.annular.RS dart,
    Finset.mem_univ _,
    edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS dart⟩, ?_⟩
  apply totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (orbitFace_incidence_le_two web.annular.RS)
    (Finset.mem_univ _) (Finset.mem_univ _)
    (dartOrbitFace_ne_alpha web dart hface)
  · exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS dart
  · rw [← web.annular.RS.edge_alpha dart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha dart)

/-- If an edge of an interior face also occurs on a different quotient face,
that face is exactly the face of the opposite dart.  This is the local form of
the usual two-sided-face lookup: it needs the source face to be simple, not
every face of the open tangle. -/
theorem alpha_face_eq_of_mem_other
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces)
    (other : OrbitFace web.annular.RS)
    (hedge : web.annular.RS.edgeOf dart ∈
      orbitFaceBoundary web.annular.RS other)
    (hne : dartOrbitFace web.annular.RS dart ≠ other) :
    dartOrbitFace web.annular.RS (web.annular.RS.alpha dart) = other := by
  have hcurrent : web.annular.RS.edgeOf dart ∈
      orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS dart) :=
    edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS dart
  have hopposite : web.annular.RS.edgeOf dart ∈
      orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS (web.annular.RS.alpha dart)) := by
    rw [← web.annular.RS.edge_alpha dart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha dart)
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      (Finset.mem_univ _)
      (Finset.mem_univ _)
      (Finset.mem_univ _)
      (dartOrbitFace_ne_alpha web dart hface) hcurrent hopposite hedge
  rcases hcases with hotherCurrent | hotherOpposite
  · exact (hne hotherCurrent.symm).elim
  · exact hotherOpposite.symm

/-- Cyclic positions on an interior face have distinct boundary edges. -/
theorem faceCycleEdge_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (root : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS root ∈
      web.annular.cellulation.interiorFaces) :
    Function.Injective (faceCycleEdge web.annular.RS root) :=
  faceCycleEdge_injective_of_boundarySimple web.annular.RS root
    (boundary_card_eq_darts_card web root hface)

/-- Every boundary edge of an interior face has a unique cyclic position. -/
theorem existsUnique_faceCycleEdge_eq
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
    (boundary_card_eq_darts_card web root hface) edge hedge

end InteriorFace

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
