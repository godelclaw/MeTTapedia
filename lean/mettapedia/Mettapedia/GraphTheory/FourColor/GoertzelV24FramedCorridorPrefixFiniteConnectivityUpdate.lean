import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixSeamConnectivityFactor

/-!
# The finite connectivity update of one source Cell

The source-facing cumulative profile before a Cell needs one fixed terminal:
the shared rung through which a tracked strand may enter the Cell.  The
six-edge Cell profile and this terminal-aware incoming profile determine the
two-edge residual seam, hence the complete outgoing crossing-to-crossing
connectivity coordinate.

This is the `L7` connectivity component of the joint finite-state update.  It
does not identify overlapping observation windows with serial generators, and
it does not claim that connectivity alone determines the remaining face and
length coordinates of the outgoing profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixFiniteConnectivityUpdateEdgeSetDecidableEq :
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

/-- The connectivity coordinate of a finite one-Cell update.  The relation is
computed from the terminal-aware incoming profile, the six-edge Cell profile,
and the residual seam whose two possible edges are themselves profile-derived.
-/
def LocalLayerFiniteConnectivityUpdate
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (output : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∀ (pair : TrackedColorPair) (first second : Fin 2),
    output.profile.strandConnected pair (.inl first) (.inl second) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (output.profile.edgeColor first).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (output.profile.edgeColor second).toColor ∧
        Relation.ReflTransGen
          (aligned.localLayerFiniteProfileComponentStep incoming cellProfile
            pair)
          ⟨aligned.toInterface.nextLocalLayerPrefixCrossing first,
            aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
              first⟩
          ⟨aligned.toInterface.nextLocalLayerPrefixCrossing second,
            aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
              second⟩

/-- The actual graph-derived profiles satisfy the fully finite connectivity
update.  In particular, neither the cumulative prefix graph nor the ambient
color function occurs in the relation after its input and Cell profiles have
been formed. -/
theorem localLayerFiniteConnectivityUpdate
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    aligned.LocalLayerFiniteConnectivityUpdate
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color
        hleftColor)
      (aligned.localLayerCellBoundaryProfile color hcolor)
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        hrightColor) := by
  intro pair first second
  rw [aligned.localLayerRightPrefixBoundedProfile_strandConnected_eq_true_iff
    color hrightColor]
  have hconnectivity :
      Relation.ReflTransGen
          (aligned.localLayerTrackedComponentStep color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
          (aligned.toInterface.nextLocalLayerPrefixCrossing first)
          (aligned.toInterface.nextLocalLayerPrefixCrossing second) ↔
        Relation.ReflTransGen
          (aligned.localLayerFiniteProfileComponentStep
            (aligned.localLayerLeftPrefixSharedRungBoundedProfile color
              hleftColor)
            (aligned.localLayerCellBoundaryProfile color hcolor) pair)
          ⟨aligned.toInterface.nextLocalLayerPrefixCrossing first,
            aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
              first⟩
          ⟨aligned.toInterface.nextLocalLayerPrefixCrossing second,
            aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
              second⟩ := by
    rw [← aligned.localLayerRightPrefixTrackedGraph_reachable_iff_componentClosure]
    exact aligned.localLayerRightPrefixTrackedGraph_reachable_iff_finiteProfileClosure
      hcubic hrotation color hcolor hleftColor pair first second
  rw [hconnectivity]
  rw [aligned.localLayerRightPrefixBoundedProfile_edgeColor_toColor
    color hrightColor first]
  rw [aligned.localLayerRightPrefixBoundedProfile_edgeColor_toColor
    color hrightColor second]

/-- Tait nonzeroness discharges both displayed cut-color premises, so the
source-facing update needs no hypothesis beyond the established geometric
and coloring data. -/
theorem localLayerFiniteConnectivityUpdate_of_tait
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) :
    aligned.LocalLayerFiniteConnectivityUpdate
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color
        (fun step => hcolor
          (aligned.toInterface.localLayerPrefixCrossing step)))
      (aligned.localLayerCellBoundaryProfile color hcolor)
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        (fun step => hcolor
          (aligned.toInterface.nextLocalLayerPrefixCrossing step))) := by
  exact aligned.localLayerFiniteConnectivityUpdate hcubic hrotation color
    hcolor
    (fun step => hcolor (aligned.toInterface.localLayerPrefixCrossing step))
    (fun step => hcolor
      (aligned.toInterface.nextLocalLayerPrefixCrossing step))

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
