import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutHoleRetention
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

/-!
# Retaining a full face boundary across a source crosscut

The source splice keeps its named holes outside the pumped strip.  This file
packages the graph-level step needed for that claim: one retained facial dart,
together with cut avoidance by the entire face boundary, retains every dart of
that face.  It applies equally to open boundary faces, so it deliberately uses
a closed facial walk rather than the two-sided facial-trail refinement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24OrbitFaceWalk
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sourceCrosscutFaceRetentionGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- A source-face boundary stays on the retained component side when a rooted
facial walk starts on that side and no boundary edge crosses the source cut. -/
theorem SourceCrosscutBoundaryData.face_vertex_mem_componentSide_of_root_and_boundary_avoids_primalCut
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
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

/-- A comparison walk from the retained side to one dart of a facial boundary
puts that whole boundary on the retained side when neither the comparison
walk nor the face boundary crosses the source cut.  This is the graph-level
form of the source's ``both holes lie outside the pumped region by
construction'' check: the source formation must construct the comparison
walk, while this lemma transports it through the finite deletion and facial
walk calculi. -/
theorem SourceCrosscutBoundaryData.face_vertex_mem_componentSide_of_bridge_and_boundary_avoids_primalCut
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
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

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
