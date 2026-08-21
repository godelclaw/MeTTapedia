import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteOneCellSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCodec

/-!
# A sound finite step for reachable source-prefix profiles

The exact source word is heterogeneous: each literal Cell has its own support
relation.  For a finite closure computation we only need a sound common
over-approximation.  The joint receipt from the one-Cell development supplies
one: retain a terminal-aware incoming profile, require that forgetting its
shared-rung terminal gives the current cumulative state, and check the complete
five-coordinate receipt for the outgoing state.

This file packages that homogeneous step both on raw three-face profiles and
on the executable `191184`-state codec.  The direction proved here is the one
needed for a safe upper bound: every actual literal Cell step is admitted.
Spurious receipt steps may remain, so a measured closure can be larger than
the true reachable set; it can never omit a source transition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedCorridorReachableProfileStep

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat
open GoertzelV24FramedTrail
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24WidthTwoPortIncidenceCodec
open GoertzelV24WidthTwoPortIncidenceCompression
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding.SourceConsecutiveSlabInterface
open SimpleGraphDartRotation

/-- Homogeneous raw step obtained by existentially retaining the one shared-
rung terminal used by the exact one-Cell receipt. -/
def LocalLayerFiniteReceiptStep
    (current next : BoundedCorridorCutProfile 2 0 3) : Prop :=
  ∃ incoming : BoundedCorridorCutProfile 2 1 3,
    forgetBoundedTerminals incoming = current ∧
      GoertzelV24FramedTrail.LocalLayerFiniteOneCellReceiptThree incoming next

/-- The executable step on the lossless three-face codec. -/
def LocalLayerFiniteReceiptCodeStep
    (current next : BoundedWidthTwoPortIncidenceProfile 3) : Prop :=
  LocalLayerFiniteReceiptStep
    (decodePortIncidenceBounded current)
    (decodePortIncidenceBounded next)

/-- Forgetting terminals commutes with narrowing the proof-carrying face
bound.  Neither operation changes the stored face-fragment coordinate. -/
@[simp] theorem forgetBoundedTerminals_narrowFaceFragmentBound
    {crossingEdgeCount terminalCount oldBound newBound : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      oldBound)
    (hbound : profile.faceFragmentCount.val ≤ newBound) :
    forgetBoundedTerminals (narrowFaceFragmentBound profile hbound) =
      narrowFaceFragmentBound (forgetBoundedTerminals profile) (by
        simpa using hbound) := by
  cases profile
  rfl

/-- Any raw receipt step transports exactly to the executable code relation.
This uses the codec equivalence, not a lossy projection. -/
theorem localLayerFiniteReceiptCodeStep_of_raw
    (current next : BoundedCorridorCutProfile 2 0 3)
    (hcurrent : BoundedIsPortIncidenceSemantic current)
    (hnext : BoundedIsPortIncidenceSemantic next)
    (hstep : LocalLayerFiniteReceiptStep current next) :
    LocalLayerFiniteReceiptCodeStep
      (compressPortIncidenceBounded current hcurrent)
      (compressPortIncidenceBounded next hnext) := by
  simpa [LocalLayerFiniteReceiptCodeStep,
    decodePortIncidenceBounded_compressPortIncidenceBounded]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorReachableProfileStepEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace GoertzelV24FramedTrail

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

/-- Every actual Tait-colored literal Cell is a step of the finite
over-approximation.  The current state is the complete cumulative profile on
the left cut, narrowed only in its proved face bound. -/
theorem localLayerFiniteReceiptStep_of_tait
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) :
    LocalLayerFiniteReceiptStep
      (narrowFaceFragmentBound
        (aligned.toInterface.localLayerLeftPrefixBoundedProfile color
          (fun step => hcolor
            (aligned.toInterface.localLayerPrefixCrossing step)))
        (aligned.toInterface
          |>.localLayerLeftPrefixBoundedProfile_faceFragmentCount_le_three
            color (fun step => hcolor
              (aligned.toInterface.localLayerPrefixCrossing step))))
      (aligned.localLayerFiniteOutputProfile color
        (fun step => hcolor
          (aligned.toInterface.nextLocalLayerPrefixCrossing step))) := by
  let hleft : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0 :=
    fun step => hcolor (aligned.toInterface.localLayerPrefixCrossing step)
  let hright : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0 :=
    fun step => hcolor (aligned.toInterface.nextLocalLayerPrefixCrossing step)
  refine ⟨aligned.localLayerFiniteInputProfile color hleft, ?_, ?_⟩
  · simp [SourceCornerAlignedSlabInterface.localLayerFiniteInputProfile]
  · exact aligned.exists_localLayerFiniteOneCellReceipt_of_tait
      hcubic hrotation color hcolor

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end

end GoertzelV24FramedCorridorReachableProfileStep

end Mettapedia.GraphTheory.FourColor
