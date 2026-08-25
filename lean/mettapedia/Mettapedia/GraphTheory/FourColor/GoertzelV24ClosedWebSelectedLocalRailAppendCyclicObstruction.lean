import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendBypass
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendComponent

/-!
# L1: the exact cyclic obstruction to a selected rail append

Loop erasure removes harmless same-track revisits from the selected Cell-3
rail append.  If one of the two remaining cross-track disjointness tests
fails, the actual collision constructs a facial-dual triangle and hence a
literal three-edge separator.  The component away from the outer hole avoids
both ordered boundaries; local cubic counting and the selected-incidence
classification then force that component to contain a cycle.

Thus the append alternative is now fail-closed at its sharpest current form:
either the two rails extend, or the code returns an actual cyclic side of the
three-edge separator.  This module does not contract a general cyclic
three-cut, identify it with the source rotor triangle, or reroute a rail, and
therefore does not claim L1 or the crosscut construction closed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- The positive obstruction returned by a failed loop-erased append: an
actual adjacent dual triangle together with a deletion component away from
the outer hole which already contains a primal cycle. -/
structure CyclicAppendObstruction
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (triangle : AdjacentDualTriangle successor) where
  component :
    (G.deleteEdges (edgeFinsetValueSet
      triangle.selectedCycle.crossingEdges)).ConnectedComponent
  outerRoot_not_mem : web.annular.RS.outer.fst ∉ component.supp
  hasCycle : HasCycleOnSide G (fun vertex => vertex ∈ component.supp)

namespace CyclicAppendObstruction

variable
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {triangle : AdjacentDualTriangle successor}

/-- The obstruction separator consists of exactly three selected primal
crossings. -/
theorem crossingEdges_card_eq_three
    (_obstruction : CyclicAppendObstruction successor triangle) :
    triangle.selectedCycle.crossingEdges.card = 3 :=
  triangle.crossingEdges_card_eq_three

/-- Every named inner boundary stub lies outside the returned cyclic side. -/
theorem innerStub_not_mem_component
    (obstruction : CyclicAppendObstruction successor triangle) (inner : Fin 5) :
    data.innerStub inner ∉ obstruction.component.supp :=
  triangle.innerStub_not_mem_component obstruction.component
    obstruction.outerRoot_not_mem inner

/-- Every named outer boundary stub lies outside the returned cyclic side. -/
theorem outerStub_not_mem_component
    (obstruction : CyclicAppendObstruction successor triangle) (outer : Fin 5) :
    data.outerStub outer ∉ obstruction.component.supp :=
  triangle.outerStub_not_mem_component obstruction.component
    obstruction.outerRoot_not_mem outer

end CyclicAppendObstruction

end SeparatedSelectedSourceLocalRailSuccessor

namespace SelectedSourceLocalRailAssembly

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}

/-- **L1 exact loop-erased cyclic alternative.**  Either the selected rails
extend across the next Cell-3 placement, or an actual cross-track collision
returns a three-edge separator with a cyclic side disjoint from both ordered
hole boundaries. -/
noncomputable def appendLocalSuccessorBypass_or_cyclicObstruction
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    Nonempty (SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)) ∨
    ∃ triangle :
        SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle successor,
      Nonempty
        (SeparatedSelectedSourceLocalRailSuccessor.CyclicAppendObstruction
          successor triangle) := by
  rcases appendLocalSuccessorBypass_or_crossCollision successor left with
    assembly | collision
  · exact Or.inl assembly
  · rcases collision with ⟨collision⟩
    let triangle := collision.toAdjacentDualTriangle
    rcases triangle.exists_component_away_from_outerRoot with
      ⟨component, hroot⟩
    exact Or.inr ⟨triangle, ⟨{
      component := component
      outerRoot_not_mem := hroot
      hasCycle := triangle.hasCycleOnSide component hroot
    }⟩⟩

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
