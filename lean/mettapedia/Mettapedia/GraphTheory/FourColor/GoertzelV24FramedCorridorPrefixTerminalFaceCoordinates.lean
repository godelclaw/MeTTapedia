import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixTerminalConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRestriction

/-!
# Terminal-aware face coordinates at one source Cell

The finite connectivity factorization retains the shared rung as one genuine
incoming terminal.  Face identity, crossing incidence, and capped face
progress must nevertheless refer to the same incoming state used by that
factorization.  This file proves the exact compatibility statement: forgetting
the shared-rung terminal recovers the established cumulative-prefix profile.

Thus terminal augmentation changes only the connectivity/incidence queries
that mention the new terminal.  It does not change the fragment carrier or
any of the three crossing-only face coordinates.  This is an `L7` interface
alignment theorem, not yet the joint finite one-Cell transfer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixTerminalFaceCoordinatesEdgeSetDecidableEq :
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

/-- Forgetting the one shared-rung terminal from the refined incoming state
recovers the established crossing-only cumulative-prefix state exactly. -/
@[simp] theorem forgetBoundedTerminals_localLayerLeftPrefixSharedRungBoundedProfile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0) :
    forgetBoundedTerminals
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor) =
      aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor := by
  unfold forgetBoundedTerminals
  unfold localLayerLeftPrefixSharedRungBoundedProfile
  unfold SourceConsecutiveSlabInterface.localLayerLeftPrefixBoundedProfile
  unfold GoertzelV24RegionalBoundaryProfileFiniteState.regionalBoundaryBoundedProfile
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  exact regionalProfile_forgetTerminals_withTerminalEdges
    aligned.toInterface.localLayerLeftPrefixGraphCutData
    aligned.localLayerLeftPrefixSharedRungTerminalEdge color hcolor

/-- The refined input has exactly the same finite face-fragment count as the
crossing-only source profile. -/
@[simp] theorem localLayerLeftPrefixSharedRungBoundedProfile_faceFragmentCount
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0) :
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).faceFragmentCount =
      (aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor).faceFragmentCount :=
  rfl

/-- Terminal augmentation preserves the occurrence-sensitive ambient-face
equivalence coordinate. -/
@[simp] theorem localLayerLeftPrefixSharedRungBoundedProfile_faceContinues
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (left right : Fin
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).faceFragmentCount.val) :
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).profile.faceContinues left right =
      (aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor).profile.faceContinues left right :=
  rfl

/-- Terminal augmentation preserves crossing-to-fragment incidence.  The
additional terminal column remains available separately for the shared rung. -/
@[simp] theorem localLayerLeftPrefixSharedRungBoundedProfile_fragmentContainsCrossing
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (fragment : Fin
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).faceFragmentCount.val)
    (crossing : Fin 2) :
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).profile.fragmentContainsPort fragment (.inl crossing) =
      (aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor).profile.fragmentContainsPort fragment (.inl crossing) :=
  rfl

/-- Terminal augmentation preserves every capped face-progress coordinate. -/
@[simp] theorem localLayerLeftPrefixSharedRungBoundedProfile_faceLengthCap
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (fragment : Fin
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).faceFragmentCount.val) :
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).profile.faceLengthCap fragment =
      (aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor).profile.faceLengthCap fragment :=
  rfl

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
