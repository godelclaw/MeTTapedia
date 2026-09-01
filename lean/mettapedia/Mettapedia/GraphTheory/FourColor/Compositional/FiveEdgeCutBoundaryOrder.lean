import Mettapedia.GraphTheory.FourColor.Compositional.FiveEdgeCutBoundaryPrerequisites
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBondBoundary

/-!
# Cyclic boundary order of an exact five-edge cut

For an exact cyclic five-edge cut in a spherical graph-backed map, the
deleted-side first-return permutation is a single five-cycle.  The only other
fixed-point-free cycle type on five points contains a two-cycle.  Such a
two-cycle would make its two boundary edges a primal separating pair, while a
third undeleted cut edge still joins the connected shores.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FiveEdgeCutBoundaryOrder

open Equiv Equiv.Perm
open FiveEdgeCutBoundaryPrerequisites
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24CyclicBondBoundary
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The deleted-side boundary successor of an exact cyclic five-cut is a
single cycle. -/
theorem deletedBoundarySuccessor_sameCycle_of_exactCyclicFiveCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 5) :
    ∀ first second : BoundaryDart graphData.toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut)),
      (deletedRegionBoundarySuccessor graphData.toRotationSystem
        (cyclicCutVertexSide cut)).SameCycle first second := by
  let RS := graphData.toRotationSystem
  let deleted := cyclicCutVertexSide cut
  let successor := deletedRegionBoundarySuccessor RS deleted
  have hsides := induce_both_sides_connected_of_card_eq_five
    hconnected hcyclic cut hcard
  have hboundaryCard : Fintype.card
      (BoundaryDart RS (deletedRegionKeep deleted)) = 5 := by
    exact card_boundaryDart_cyclicCutVertexSide_eq_five
      graphData cut hcard
  have hfixed : ∀ boundary : BoundaryDart RS
      (deletedRegionKeep deleted), successor boundary ≠ boundary := by
    exact deletedBoundarySuccessor_fixedPointFree RS deleted htwoSided
  rcases fixedPointFree_perm_card_five_transitive_or_twoCycle
      successor hboundaryCard hfixed with htransitive | htwoCycle
  · exact htransitive
  · rcases htwoCycle with ⟨first, hfirstNe, hfirstTwoCycle⟩
    let second := successor first
    let left := dartOrbitFace RS first.1.1
    let right := dartOrbitFace RS (RS.alpha first.1.1)
    have hfacePair := twoCycle_boundaryEdges_share_face_pair
      RS deleted htwoSided first hfirstNe hfirstTwoCycle
    change left ≠ right ∧ RS.edgeOf first.1.1 ≠ RS.edgeOf second.1.1 ∧
        RS.edgeOf first.1.1 ∈ orbitFaceBoundary RS left ∧
        RS.edgeOf first.1.1 ∈ orbitFaceBoundary RS right ∧
        RS.edgeOf second.1.1 ∈ orbitFaceBoundary RS left ∧
        RS.edgeOf second.1.1 ∈ orbitFaceBoundary RS right at hfacePair
    rcases hfacePair with
      ⟨hfaces, hedgesNe, hfirstLeft, hfirstRight,
        hsecondLeft, hsecondRight⟩
    have hprimal : (rotationPrimalGraph RS).Connected := by
      change (rotationPrimalGraph graphData.toRotationSystem).Connected
      rw [rotationPrimalGraph_toRotationSystem_eq]
      exact hconnected
    have hdual := orbitFaceInteriorDual_connected
      RS hsphere.cubic hprimal hrotation
    have hseparator :=
      not_connected_deleteEdges_pair_of_shared_face_pair
        graphData htwoSided hdual hconnected hsphere hfaces hedgesNe
        hfirstLeft hfirstRight hsecondLeft hsecondRight
    have hfirstCut : RS.edgeOf first.1.1 ∈ cut.edgeCut := by
      rw [← vertexSetCrossingEdges_cyclicCutVertexSide graphData cut]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges
        RS deleted first
    have hsecondCut : RS.edgeOf second.1.1 ∈ cut.edgeCut := by
      rw [← vertexSetCrossingEdges_cyclicCutVertexSide graphData cut]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges
        RS deleted second
    have hstillConnected :=
      deleteEdges_pair_connected_of_exactCyclicFiveCut cut hcard
        hsides.1 hsides.2
        (RS.edgeOf first.1.1) (RS.edgeOf second.1.1)
        hfirstCut hsecondCut hedgesNe
    exact (hseparator hstillConnected).elim

/-- The actual first-return orders on the complementary shores of an exact
cyclic five-edge cut have opposite orientation. -/
theorem retainedBoundarySuccessor_eq_deleted_inverse_of_exactCyclicFiveCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 5) :
    retainedRegionBoundarySuccessor graphData.toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut)) =
      (deletedRegionBoundarySuccessor graphData.toRotationSystem
        (cyclicCutVertexSide cut))⁻¹ := by
  have hsides := induce_both_sides_connected_of_card_eq_five
    hconnected hcyclic cut hcard
  have hkeep : deletedRegionKeep (cyclicCutVertexSide cut) =
      (fun vertex ↦ ¬ cut.side vertex) := by
    funext vertex
    simp [deletedRegionKeep, mem_cyclicCutVertexSide_iff]
  have hdeleted :
      (fun vertex ↦ ¬ deletedRegionKeep
        (cyclicCutVertexSide cut) vertex) = cut.side := by
    funext vertex
    simp [deletedRegionKeep, mem_cyclicCutVertexSide_iff]
  apply retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
    graphData (cyclicCutVertexSide cut) hsphere htwoSided hconnected hrotation
  · rw [hkeep]
    exact hsides.2
  · rw [hdeleted]
    exact hsides.1

/-- An exact cyclic five-edge cut has genuine cyclic boundary coordinates.
The deleted-side order is positive rotation and the retained-side order is
its inverse. -/
theorem exists_boundaryOrder_of_exactCyclicFiveCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 5) :
    ∃ boundaryOrder : Fin 5 ≃
        BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut)),
      deletedRegionBoundarySuccessor graphData.toRotationSystem
          (cyclicCutVertexSide cut) =
        boundaryOrder.permCongr (finRotate 5) ∧
      retainedRegionBoundarySuccessor graphData.toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut)) =
        (boundaryOrder.permCongr (finRotate 5))⁻¹ := by
  let successor := deletedRegionBoundarySuccessor
    graphData.toRotationSystem (cyclicCutVertexSide cut)
  have hboundaryCard : Fintype.card
      (BoundaryDart graphData.toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))) = 5 :=
    card_boundaryDart_cyclicCutVertexSide_eq_five graphData cut hcard
  have htransitive : ∀ first second,
      successor.SameCycle first second :=
    deletedBoundarySuccessor_sameCycle_of_exactCyclicFiveCut
      graphData hsphere htwoSided hconnected hrotation hcyclic cut hcard
  rcases transitive_perm_card_five_exists_finRotate_coordinate
      successor hboundaryCard htransitive with ⟨boundaryOrder, horder⟩
  refine ⟨boundaryOrder, horder, ?_⟩
  rw [retainedBoundarySuccessor_eq_deleted_inverse_of_exactCyclicFiveCut
    graphData hsphere htwoSided hconnected hrotation hcyclic cut hcard]
  change successor⁻¹ = (boundaryOrder.permCongr (finRotate 5))⁻¹
  rw [horder]

/-- Package the retained shore of an exact cyclic five-edge cut as the
generic cyclic-bond interface consumed by the physical Kempe theory. -/
theorem exists_cyclicBondBoundaryData_of_exactCyclicFiveCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 5) :
    Nonempty (CyclicBondBoundaryData graphData.toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut))) := by
  let RS := graphData.toRotationSystem
  let deleted := cyclicCutVertexSide cut
  let retained := retainedRegionBoundarySuccessor RS
    (deletedRegionKeep deleted)
  let successor := deletedRegionBoundarySuccessor RS deleted
  have hboundaryCard : Fintype.card
      (BoundaryDart RS (deletedRegionKeep deleted)) = 5 :=
    card_boundaryDart_cyclicCutVertexSide_eq_five graphData cut hcard
  have hsuccessorTransitive : ∀ first second,
      successor.SameCycle first second :=
    deletedBoundarySuccessor_sameCycle_of_exactCyclicFiveCut
      graphData hsphere htwoSided hconnected hrotation hcyclic cut hcard
  have hretainedEq : retained = successor⁻¹ := by
    exact retainedBoundarySuccessor_eq_deleted_inverse_of_exactCyclicFiveCut
      graphData hsphere htwoSided hconnected hrotation hcyclic cut hcard
  have hretainedTransitive : ∀ first second,
      retained.SameCycle first second := by
    intro first second
    rw [hretainedEq, sameCycle_inv]
    exact hsuccessorTransitive first second
  rcases transitive_perm_card_five_exists_finRotate_coordinate
      retained hboundaryCard hretainedTransitive with
    ⟨boundaryOrder, horder⟩
  exact ⟨
    { length := 5
      two_le_length := by omega
      order := boundaryOrder
      successor_eq := horder.symm }⟩

end

end FiveEdgeCutBoundaryOrder

end Mettapedia.GraphTheory.FourColor.Compositional
