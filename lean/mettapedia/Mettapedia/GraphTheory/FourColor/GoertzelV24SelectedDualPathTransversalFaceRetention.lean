import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalSpliceBoundary

/-!
# Face retention for selected transversal boundaries

A walk which avoids the literal selected primal cut cannot leave its deletion
component.  Consequently, once one dart of a face is retained and the whole
face boundary avoids the cut, every dart of that face is retained.  This is
the selected-edge counterpart of the historical crosscut retention API and
does not require globally unique shared face edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24OrbitFaceWalk
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance selectedFaceRetentionEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SeparatedAlignedSelectedDualTransversals

/-- Every vertex of an ambient walk avoiding the selected primal support lies
on the same component side as the initial vertex. -/
theorem SourceSelectedBoundaryData.walk_support_subset_componentSide_of_avoids_primalCut
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    {walkStart walkFinish : V} (walk : G.Walk walkStart walkFinish)
    (hstart : walkStart ∈ boundary.component.supp)
    (havoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges →
      edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data))
    {vertex : V} (hvertex : vertex ∈ walk.support) :
    vertex ∈ pair.componentSide boundary.component := by
  let walkPrefix := walk.takeUntil vertex hvertex
  have hprefixAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ walkPrefix.edges →
        edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data) := by
    intro edge hedge
    exact havoid edge (walk.edges_takeUntil_subset_edges hvertex hedge)
  have hside := component_side_iff_of_walk_avoiding_removed
    (pair.primalCutEdges data) boundary.component walkPrefix hprefixAvoid
  exact (pair.mem_componentSide_iff boundary.component vertex).2
    (hside.mp hstart)

/-- A rooted facial walk transports retention to every dart of that face. -/
theorem SourceSelectedBoundaryData.face_vertex_mem_componentSide_of_root_and_boundary_avoids_primalCut
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (root dart : G.Dart)
    (hroot : root.fst ∈ boundary.component.supp)
    (havoid : ∀ edge : G.edgeSet,
      edge ∈ orbitFaceBoundary data.toRotationSystem
        (dartOrbitFace data.toRotationSystem root) →
      edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data))
    (hdart : dartOrbitFace data.toRotationSystem dart =
      dartOrbitFace data.toRotationSystem root) :
    dart.fst ∈ pair.componentSide boundary.component := by
  rcases exists_rootedFaceWalk data root with
    ⟨walk, hwalkDarts, hwalkBoundary⟩
  apply boundary.walk_support_subset_componentSide_of_avoids_primalCut
    data pair walk hroot
  · intro edge hedge
    exact havoid edge (hwalkBoundary edge hedge)
  · apply walk.dart_fst_mem_support_of_mem_darts
    rw [hwalkDarts]
    exact (mem_faceOrbitDarts_iff data root dart).2 hdart

/-- A comparison walk from an already-retained dart to one dart of a face,
together with boundary avoidance, retains the entire target face. -/
theorem SourceSelectedBoundaryData.face_vertex_mem_componentSide_of_bridge_and_boundary_avoids_primalCut
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (source root dart : G.Dart)
    (bridge : G.Walk source.fst root.fst)
    (hsource : source.fst ∈ boundary.component.supp)
    (hbridgeAvoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ bridge.edges →
      edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data))
    (hboundaryAvoid : ∀ edge : G.edgeSet,
      edge ∈ orbitFaceBoundary data.toRotationSystem
        (dartOrbitFace data.toRotationSystem root) →
      edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data))
    (hdart : dartOrbitFace data.toRotationSystem dart =
      dartOrbitFace data.toRotationSystem root) :
    dart.fst ∈ pair.componentSide boundary.component := by
  have hrootSide : root.fst ∈ pair.componentSide boundary.component := by
    apply boundary.walk_support_subset_componentSide_of_avoids_primalCut
      data pair bridge hsource hbridgeAvoid
    exact bridge.end_mem_support
  have hroot : root.fst ∈ boundary.component.supp :=
    (pair.mem_componentSide_iff boundary.component root.fst).1 hrootSide
  exact boundary.face_vertex_mem_componentSide_of_root_and_boundary_avoids_primalCut
    data pair root dart hroot hboundaryAvoid hdart

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
