import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileConnectivityUpdate

/-!
# Finite-profile connectivity relation for one source Cell

The graph-level source-Cell update is already the closure of old-prefix
components, new-hexagon components, and the two classified seam turns.  This
file identifies the actual outgoing `strandConnected` coordinate with that
same relational closure.

No successor profile is chosen and no determinism is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileConnectivityRelationEdgeSetDecidableEq :
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

/-- The actual outgoing connectivity bit is true exactly when both queried
crossings carry the tracked color pair and the source's three-factor
one-Cell relation connects them. -/
theorem localLayerRightPrefixBoundedProfile_strandConnected_eq_true_iff
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    (((aligned.toInterface.localLayerRightPrefixBoundedProfile color hcolor)
        |>.profile.strandConnected pair (.inl left) (.inl right)) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.toInterface.nextLocalLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.toInterface.nextLocalLayerPrefixCrossing right)) ∧
        Relation.ReflTransGen
          (aligned.localLayerTrackedComponentStep color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
          (aligned.toInterface.nextLocalLayerPrefixCrossing left)
          (aligned.toInterface.nextLocalLayerPrefixCrossing right) := by
  let interface := aligned.toInterface
  let data := interface.localLayerRightPrefixGraphCutData
  change
    ((data.regionalProfile color hcolor).strandConnected pair
        (.inl left) (.inl right) = true) ↔ _
  rw [data.regionalProfile_strandConnected_eq_true_iff]
  have hleft : data.portEdge (.inl left) ∈ data.regionEdges :=
    interface.localLayerRightPrefixGraphCutData_portsInRegion (.inl left)
  have hright : data.portEdge (.inl right) ∈ data.regionEdges :=
    interface.localLayerRightPrefixGraphCutData_portsInRegion (.inl right)
  simp only [hleft, hright, true_and]
  change
    IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (interface.nextLocalLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (interface.nextLocalLayerPrefixCrossing right)) ∧
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          interface.localLayerRightPrefixRegion color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            (interface.nextLocalLayerPrefixCrossing left)
            (interface.nextLocalLayerPrefixCrossing right) ↔ _
  rw [aligned.localLayerRightPrefixTrackedGraph_reachable_iff_componentClosure]

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
