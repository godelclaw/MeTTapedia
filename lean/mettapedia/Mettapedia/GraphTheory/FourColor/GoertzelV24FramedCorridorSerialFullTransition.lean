import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialFaceTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialTrackedTransition

/-!
# A finite five-coordinate transition for one literal serial Cell

The compositional source profile has three conceptual coordinates: boundary
colours, tracked two-colour connectivity, and capped face progress.  The Lean
profile refines the last coordinate into face continuation, port incidence,
and capped length.  This file packages the finite transition data for all five
Lean fields in one witness.

The tracked part retains a Boolean residue for a component which meets no
displayed input coordinate.  The facial part similarly retains one capped
old-prefix residue.  These are deliberate finite summaries of information
outside the displayed cut, not assumptions that the displayed ports are a
complete frontier.

Every literal source Cell produces this finite witness.  This remains the
source-image direction: no converse realization theorem, executable reachable
closure, or numerical `V₀` is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

/-- All finite data attached to one literal width-two serial transition. -/
structure BoundedSerialFullTransitionCode
    (inputCount outputCount : Nat) where
  outputEdgeColor : Fin 2 → StrandColor
  tracked : BoundedSerialTrackedTransitionCode
  face : BoundedSerialFaceTransitionCode inputCount outputCount

noncomputable instance (inputCount outputCount : Nat) :
    DecidableEq (BoundedSerialFullTransitionCode inputCount outputCount) :=
  Classical.decEq _

private def boundedSerialFullTransitionCodeEquiv
    (inputCount outputCount : Nat) :
    BoundedSerialFullTransitionCode inputCount outputCount ≃
      (Fin 2 → StrandColor) × BoundedSerialTrackedTransitionCode ×
        BoundedSerialFaceTransitionCode inputCount outputCount where
  toFun code := ⟨code.outputEdgeColor, code.tracked, code.face⟩
  invFun code :=
    { outputEdgeColor := code.1
      tracked := code.2.1
      face := code.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (inputCount outputCount : Nat) :
    Fintype (BoundedSerialFullTransitionCode inputCount outputCount) :=
  Fintype.ofEquiv _
    (boundedSerialFullTransitionCodeEquiv inputCount outputCount).symm

/-- The joint finite relation on all five profile fields.  The edge-colour
coordinate is explicit; the tracked code governs `strandConnected`; and the
face code governs continuation, port incidence, and capped progress. -/
def BoundedSerialFullTransition
    (input output : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∃ code : BoundedSerialFullTransitionCode input.faceFragmentCount.val
      output.faceFragmentCount.val,
    (∀ step, output.profile.edgeColor step = code.outputEdgeColor step) ∧
    (∀ (pair : TrackedColorPair) (left right : Fin 2),
      (output.profile.strandConnected pair (.inl left) (.inl right) = true) ↔
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (output.profile.edgeColor left).toColor ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (output.profile.edgeColor right).toColor ∧
          (code.tracked.hiddenConnected pair left right = true ∨
            ∃ inputLeft inputRight : Fin 2,
              code.tracked.usesInput pair left inputLeft = true ∧
                input.profile.strandConnected pair
                    (.inl inputLeft) (.inl inputRight) = true ∧
                code.tracked.usesInput pair right inputRight = true)) ∧
    (∀ left right,
      output.profile.faceContinues left right =
        code.face.outputFaceContinues left right) ∧
    (∀ fragment port,
      output.profile.fragmentContainsPort fragment port =
        code.face.outputFragmentContainsPort fragment port) ∧
    (∀ fragment,
      (output.profile.faceLengthCap fragment).val =
        code.face.outputCap input.profile.faceLengthCap fragment)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFullTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The two graph-derived profiles around every literal source Cell satisfy
one joint finite transition which updates all five profile coordinates. -/
theorem sourceCorridorSerialBoundedProfiles_fullTransition
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hinputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0)
    (houtputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0) :
    BoundedSerialFullTransition
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hinputColor)
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color houtputColor) := by
  let input := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor
  let output := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color houtputColor
  rcases sourceCorridorSerialBoundedProfiles_trackedTransition realization
      hcubic hrotation htwoSided hunique offset color hinputColor houtputColor
    with ⟨tracked, htracked⟩
  rcases sourceCorridorSerialBoundedProfiles_faceTransition realization
      hcubic hrotation htwoSided hunique offset color hinputColor houtputColor
    with ⟨face, hcontinues, hports, hcaps⟩
  change BoundedSerialFullTransition input output
  refine ⟨
    { outputEdgeColor := output.profile.edgeColor
      tracked := tracked
      face := face }, ?_, htracked, hcontinues, hports, hcaps⟩
  intro step
  rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
