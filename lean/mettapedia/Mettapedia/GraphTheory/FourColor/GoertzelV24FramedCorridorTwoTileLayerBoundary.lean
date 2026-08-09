import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailStep
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalLayerComponent

/-!
# Concrete two-tile layer boundaries in a source corridor

Each of the three source rung forms constructs a simple six-step facial-dual
boundary around two adjacent corridor tiles.  This module retains that
boundary as data, with its cycle and exact crossing count, so later corridor
assembly works with a real source layer rather than reopening a finite case
split or replacing it by a chord wall.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualCycleBond
open GoertzelV24DualCycleSeparator
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24FramedDualCycleSeparator
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sourceTwoTileLayerBoundaryGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- A literal simple layer boundary enclosing two adjacent source corridor
tiles.  The walk is selected from the real `forwardTwo`, `forwardThree`, or
`forwardFour` construction, not from an abstract planar separator. -/
structure SourceCornerAlignedTwoTileLayerBoundary
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) where
  walk : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.firstLayerFace first.toInterface.firstLayerFace
  isCycle : walk.IsCycle
  length_eq_six : walk.length = 6

/-- Choose the source's concrete two-tile boundary after its finite rung
case has been discharged.  The choice hides only a proved finite case split;
the selected walk and its cycle proof remain visible in the resulting data. -/
noncomputable def sourceCornerAlignedTwoTileLayerBoundary
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) :
    SourceCornerAlignedTwoTileLayerBoundary first second := by
  let witness := exists_sourceCornerAlignedTwoTileLayerBoundary_isCycle
    hcubic hrotation first second
  exact {
    walk := Classical.choose witness
    isCycle := (Classical.choose_spec witness).1
    length_eq_six := (Classical.choose_spec witness).2
  }

/-- The finite primal edge support crossed by a concrete two-tile source
layer boundary. -/
noncomputable def SourceCornerAlignedTwoTileLayerBoundary.cutEdges
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    boundary.walk

/-- A two-tile source boundary crosses six distinct primal edges: one for
each step of its checked simple facial-dual cycle. -/
theorem SourceCornerAlignedTwoTileLayerBoundary.cutEdges_card_eq_six
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    boundary.cutEdges.card = 6 := by
  rw [cutEdges,
    card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two embedded.cellulation.rotation.toRotationSystem)
      hunique boundary.walk boundary.isCycle,
    boundary.length_eq_six]

omit [DecidableEq V] in
/-- A nontrivial finite edge deletion in a connected graph has a nonempty
original-graph boundary whenever a different deletion component exists. -/
private theorem componentCrossingEdges_nonempty_of_distinct
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (inside outside :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    (componentCrossingEdges removed inside).Nonempty := by
  rcases inside.nonempty_supp with ⟨insideVertex, hinside⟩
  rcases outside.nonempty_supp with ⟨outsideVertex, houtside⟩
  have houtsideNotInside : outsideVertex ∉ inside.supp := by
    intro hcommon
    apply hdistinct
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hcommon houtside
  rcases hconnected insideVertex outsideVertex with ⟨walk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => vertex ∈ inside.supp) walk hinside houtsideNotInside with
    ⟨edge, _hwalkEdge, hcross⟩
  exact ⟨edge,
    (mem_componentCrossingEdges_iff removed inside edge).2 hcross⟩

/-- The concrete two-tile source boundary constructs an actual finite
deletion component whose graph boundary is exactly its six crossed primal
edges.  Thus this layer has a real retained side; it is not merely a
facial-dual drawing. -/
theorem SourceCornerAlignedTwoTileLayerBoundary.exists_component_exactBoundary
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext :
      (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    ∃ component : (G.deleteEdges
        (edgeFinsetValueSet boundary.cutEdges)).ConnectedComponent,
      componentCrossingEdges boundary.cutEdges component = boundary.cutEdges := by
  have hcut :
      dualWalkPrimalCut embedded.cellulation.rotation hunique boundary.walk =
        edgeFinsetValueSet boundary.cutEdges := by
    exact dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      embedded.cellulation.rotation hunique boundary.walk
  have hnotConnected : ¬ (G.deleteEdges
      (edgeFinsetValueSet boundary.cutEdges)).Connected := by
    rw [← hcut]
    exact not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
      embedded.cellulation.rotation
      embedded.cellulation.fullOrbitFaceInteriorDual_connected
      embedded.cellulation.connected embedded.cellulation.euler hunique
      boundary.walk boundary.isCycle
  rcases exists_distinct_components_of_not_connected
      embedded.cellulation.connected boundary.cutEdges hnotConnected with
    ⟨inside, outside, hdistinct⟩
  refine ⟨inside, ?_⟩
  have hsubset : crossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) ⊆
      boundary.cutEdges := by
    rw [← componentCrossingEdges_eq_crossingEdgeFinset boundary.cutEdges inside]
    exact componentCrossingEdges_subset_removed boundary.cutEdges inside
  have hnonempty :
      (crossingEdgeFinset G (fun vertex => vertex ∈ inside.supp)).Nonempty := by
    rw [← componentCrossingEdges_eq_crossingEdgeFinset boundary.cutEdges inside]
    exact componentCrossingEdges_nonempty_of_distinct
      embedded.cellulation.connected boundary.cutEdges inside outside hdistinct
  have hboundary : crossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) =
      boundary.cutEdges := by
    exact crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
      embedded.cellulation.rotation htwoSided hunique boundary.walk
      boundary.isCycle (fun vertex => vertex ∈ inside.supp) hsubset hnonempty
  rw [componentCrossingEdges_eq_crossingEdgeFinset]
  exact hboundary

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
