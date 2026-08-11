import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorConnectivity

/-!
# Factoring the source Cell component through its six-edge profile

The newly exposed factor is the complete boundary of the next source
hexagon.  Its established rung placement transports `Fin 6` to the actual
facial cycle, and the existing placed-hex connectivity matrix computes
tracked components on those six edges.

This module proves that the transported coordinate enumerates the literal
Cell boundary exactly and replaces every Cell-factor component move by
reflexive equality or one true matrix bit.  The residual seam remains visible
as the final local factor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixCellConnectivityFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
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

/-- The established source placement on the newly exposed central hexagon. -/
noncomputable def localLayerCellPlacement
    (_aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)

/-- The placement root is the actual next central face used by the cumulative
Cell region. -/
theorem localLayerCellPlacement_root_face
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    dartOrbitFace embedded.cellulation.rotation.toRotationSystem
        aligned.localLayerCellPlacement.root =
      aligned.toInterface.nextCenterLayerFace.1 := by
  simpa [localLayerCellPlacement,
    SourceConsecutiveSlabInterface.nextCenterLayerFace] using
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext)).root_face

/-- The six standard positions transported to actual source-graph edges. -/
noncomputable def localLayerCellBoundaryEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (position : Fin 6) : G.edgeSet :=
  faceCycleEdge embedded.cellulation.rotation.toRotationSystem
    aligned.localLayerCellPlacement.root
    (placementPositionOfSix aligned.localLayerCellPlacement position)

theorem localLayerCellBoundaryEdge_mem_cellBoundaryRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (position : Fin 6) :
    aligned.localLayerCellBoundaryEdge position ∈
      aligned.toInterface.localLayerCellBoundaryRegion := by
  change faceCycleEdge embedded.cellulation.rotation.toRotationSystem
      aligned.localLayerCellPlacement.root
        (placementPositionOfSix aligned.localLayerCellPlacement position) ∈
    orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      aligned.toInterface.nextCenterLayerFace.1
  rw [← aligned.localLayerCellPlacement_root_face]
  exact faceCycleEdge_mem embedded.cellulation.rotation.toRotationSystem
    aligned.localLayerCellPlacement.root _

theorem localLayerCellBoundaryEdge_injective
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective aligned.localLayerCellBoundaryEdge := by
  intro left right hedge
  apply Fin.cast_injective aligned.localLayerCellPlacement.orbit_card.symm
  apply faceCycleEdge_injective
    embedded.cellulation.rotation.toRotationSystem htwoSided
    aligned.localLayerCellPlacement.root
  exact hedge

/-- The transported six-position coordinate enumerates the literal newly
exposed facial boundary, with neither omissions nor duplicate edges. -/
theorem indexedLocalLayerCellBoundaryEdges_eq_cellBoundaryRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    indexedCrossingEdgeSet aligned.localLayerCellBoundaryEdge =
      aligned.toInterface.localLayerCellBoundaryRegion := by
  have hsubset :
      indexedCrossingEdgeSet aligned.localLayerCellBoundaryEdge ⊆
        aligned.toInterface.localLayerCellBoundaryRegion := by
    intro edge hedge
    rcases (mem_indexedCrossingEdgeSet_iff
      aligned.localLayerCellBoundaryEdge edge).1 hedge with
      ⟨position, rfl⟩
    exact aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion position
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
    aligned.toInterface.nextCenterLayerFace_boundary_card_eq_six,
    card_indexedCrossingEdgeSet_eq aligned.localLayerCellBoundaryEdge
      aligned.localLayerCellBoundaryEdge_injective]

/-- A selected edge belongs to the Cell factor exactly when it has one of the
six transported boundary coordinates. -/
theorem mem_finiteConnectivityInterface_inter_cellBoundary_iff_exists_position
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (edge : G.edgeSet) :
    edge ∈ aligned.localLayerFiniteConnectivityInterface ∩
        aligned.toInterface.localLayerCellBoundaryRegion ↔
      ∃ position : Fin 6, aligned.localLayerCellBoundaryEdge position = edge := by
  constructor
  · intro hedge
    have hcell := (Finset.mem_inter.1 hedge).2
    have hindexed : edge ∈
        indexedCrossingEdgeSet aligned.localLayerCellBoundaryEdge := by
      rw [aligned.indexedLocalLayerCellBoundaryEdges_eq_cellBoundaryRegion]
      exact hcell
    exact (mem_indexedCrossingEdgeSet_iff
      aligned.localLayerCellBoundaryEdge edge).1 hindexed
  · rintro ⟨position, rfl⟩
    have hcell :=
      aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion position
    exact Finset.mem_inter.2
      ⟨aligned.localLayerCellBoundaryRegion_subset_finiteConnectivityInterface
          hcell,
        hcell⟩

/-- The finite six-by-six connectivity observable of the literal source
Cell boundary. -/
def localLayerCellConnectivityProfile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color) :
    TrackedColorPair → Fin 6 → Fin 6 → Bool :=
  placedHexRegionalConnectivityProfile aligned.localLayerCellPlacement
    aligned.toInterface.localLayerCellBoundaryRegion color

/-- The Cell-factor component relation read only from the six-edge matrix.
Equality again accounts for unguarded graph reflexivity. -/
def localLayerCellProfileComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (cellProfile : TrackedColorPair → Fin 6 → Fin 6 → Bool)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) : Prop :=
  left = right ∨
    ∃ leftPosition rightPosition : Fin 6,
      aligned.localLayerCellBoundaryEdge leftPosition = left.1 ∧
        aligned.localLayerCellBoundaryEdge rightPosition = right.1 ∧
        cellProfile pair leftPosition rightPosition = true

/-- On the selected interface, literal Cell-boundary reachability is exactly
the relation computed by its six-edge connectivity matrix. -/
theorem localLayerCellTrackedGraph_reachable_iff_profileComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerCellBoundaryRegion color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left right ↔
      aligned.localLayerCellProfileComponentStep
        (aligned.localLayerCellConnectivityProfile color) pair left right := by
  let cellGraph := regionalTrackedEdgeGraph
    embedded.cellulation.rotation.toRotationSystem
    aligned.toInterface.localLayerCellBoundaryRegion color
    (trackedColorPairColors pair).1
    (trackedColorPairColors pair).2
  constructor
  · intro hreach
    by_cases heq : left = right
    · exact Or.inl heq
    · have hne : left.1 ≠ right.1 := by
        intro hval
        exact heq (Subtype.ext hval)
      have hleftSupport : left.1 ∈ cellGraph.support :=
        SimpleGraph.mem_support_of_reachable hne hreach
      have hrightSupport : right.1 ∈ cellGraph.support :=
        SimpleGraph.mem_support_of_reachable hne.symm hreach.symm
      rcases (SimpleGraph.mem_support cellGraph).1 hleftSupport with
        ⟨leftNeighbor, hleftAdj⟩
      rcases (SimpleGraph.mem_support cellGraph).1 hrightSupport with
        ⟨rightNeighbor, hrightAdj⟩
      have hleftRegion : left.1 ∈
          aligned.toInterface.localLayerCellBoundaryRegion := hleftAdj.2.1
      have hrightRegion : right.1 ∈
          aligned.toInterface.localLayerCellBoundaryRegion := hrightAdj.2.1
      rcases
          (aligned.mem_finiteConnectivityInterface_inter_cellBoundary_iff_exists_position
            left.1).1 (Finset.mem_inter.2 ⟨left.2, hleftRegion⟩) with
        ⟨leftPosition, hleftPosition⟩
      rcases
          (aligned.mem_finiteConnectivityInterface_inter_cellBoundary_iff_exists_position
            right.1).1 (Finset.mem_inter.2 ⟨right.2, hrightRegion⟩) with
        ⟨rightPosition, hrightPosition⟩
      refine Or.inr
        ⟨leftPosition, rightPosition, hleftPosition, hrightPosition, ?_⟩
      apply (placedHexRegionalConnectivityProfile_eq_true_iff
        aligned.localLayerCellPlacement
        aligned.toInterface.localLayerCellBoundaryRegion color pair
        leftPosition rightPosition).2
      change aligned.localLayerCellBoundaryEdge leftPosition ∈
          aligned.toInterface.localLayerCellBoundaryRegion ∧
        aligned.localLayerCellBoundaryEdge rightPosition ∈
          aligned.toInterface.localLayerCellBoundaryRegion ∧ _
      have hleftTracked :
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (color (aligned.localLayerCellBoundaryEdge leftPosition)) := by
        rw [hleftPosition]
        exact hleftAdj.1.2.1
      have hrightTracked :
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (color (aligned.localLayerCellBoundaryEdge rightPosition)) := by
        rw [hrightPosition]
        exact hrightAdj.1.2.1
      have hreachPositions :
          (regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            aligned.toInterface.localLayerCellBoundaryRegion color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Reachable
              (aligned.localLayerCellBoundaryEdge leftPosition)
              (aligned.localLayerCellBoundaryEdge rightPosition) := by
        rw [hleftPosition, hrightPosition]
        exact hreach
      exact ⟨aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion leftPosition,
        aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion rightPosition,
        hleftTracked, hrightTracked, hreachPositions⟩
  · intro hstep
    rcases hstep with heq |
      ⟨leftPosition, rightPosition, hleftPosition, hrightPosition, hbit⟩
    · rw [heq]
    · have hsemantic :=
        (placedHexRegionalConnectivityProfile_eq_true_iff
          aligned.localLayerCellPlacement
          aligned.toInterface.localLayerCellBoundaryRegion color pair
          leftPosition rightPosition).1 hbit
      have hreach := hsemantic.2.2.2.2
      change (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerCellBoundaryRegion color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (aligned.localLayerCellBoundaryEdge leftPosition)
          (aligned.localLayerCellBoundaryEdge rightPosition) at hreach
      rw [hleftPosition, hrightPosition] at hreach
      exact hreach

/-- The finite one-Cell move after factoring both nonlocal old-prefix
connectivity and the literal six-edge Cell connectivity. -/
def localLayerIncomingAndCellProfileFactoredComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : TrackedColorPair → Fin 6 → Fin 6 → Bool)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) : Prop :=
  aligned.localLayerOldPrefixProfileComponentStep incoming pair left right ∨
    aligned.localLayerCellProfileComponentStep cellProfile pair left right ∨
    (aligned.toInterface.localLayerTrackedSeamGraph color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).Reachable left right

/-- Actual outgoing connectivity is now the closure of two finite profile
relations and the explicit two-turn seam relation. -/
theorem localLayerRightPrefixTrackedGraph_reachable_iff_incomingAndCellProfileFactoredClosure
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerRightPrefixRegion color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
      (aligned.toInterface.nextLocalLayerPrefixCrossing left)
      (aligned.toInterface.nextLocalLayerPrefixCrossing right) ↔
    Relation.ReflTransGen
      (aligned.localLayerIncomingAndCellProfileFactoredComponentStep
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor)
        (aligned.localLayerCellConnectivityProfile color) color pair)
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing left,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          left⟩
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing right,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          right⟩ := by
  rw [aligned.localLayerRightPrefixTrackedGraph_reachable_iff_incomingProfileFactoredClosure
    hcubic hrotation color hcolor pair left right]
  constructor
  · intro hclosure
    exact hclosure.mono (by
      intro first second hstep
      rcases hstep with hfirst | hcell | hseam
      · exact Or.inl hfirst
      · exact Or.inr (Or.inl
          ((aligned.localLayerCellTrackedGraph_reachable_iff_profileComponentStep
            color pair first second).1 hcell))
      · exact Or.inr (Or.inr hseam))
  · intro hclosure
    exact hclosure.mono (by
      intro first second hstep
      rcases hstep with hfirst | hcell | hseam
      · exact Or.inl hfirst
      · exact Or.inr (Or.inl
          ((aligned.localLayerCellTrackedGraph_reachable_iff_profileComponentStep
            color pair first second).2 hcell))
      · exact Or.inr (Or.inr hseam))

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
