import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialFaceResidualCode

/-!
# A finite facial transition for one literal serial Cell

The cumulative source profile and the profile after one literal Cell both
live on the bounded width-two carrier.  This file packages all three facial
coordinates of that transition in one finite witness:

* occurrence-sensitive face continuation;
* fragment/port incidence; and
* capped face progress.

The cap update is not copied from the output state.  It is decoded from the
input profile, the occurrence-sensitive input-use matrix, one capped
old-prefix residue, and the literal-Cell/overlap caps.  Thus the only
old-prefix information retained by the witness is finite.

Every actual source Cell produces such a witness.  The converse statement
that every abstract witness is realized by a literal source Cell is not
asserted here; consequently this is the sound finite-image direction needed
before an exact executable support relation, not yet that support relation or
a reachable-closure computation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraphDartRotation

/-- Finite facial data carried by one transition between exact fragment
carriers.  The two output Boolean tables are retained because they are
independent manuscript coordinates, while the output cap is reconstructed
below rather than stored. -/
structure BoundedSerialFaceTransitionCode
    (inputCount outputCount : Nat) where
  usesInput : Fin outputCount → Fin inputCount → Bool
  residueCap : Fin outputCount → Fin 6
  localCap : Fin outputCount → Fin 6
  overlapCap : Fin outputCount → Fin 6
  outputFaceContinues : Fin outputCount → Fin outputCount → Bool
  outputFragmentContainsPort : Fin outputCount → CorridorPort 2 0 → Bool

noncomputable instance (inputCount outputCount : Nat) :
    DecidableEq (BoundedSerialFaceTransitionCode inputCount outputCount) :=
  Classical.decEq _

private def boundedSerialFaceTransitionCodeEquiv
    (inputCount outputCount : Nat) :
    BoundedSerialFaceTransitionCode inputCount outputCount ≃
      (Fin outputCount → Fin inputCount → Bool) ×
      (Fin outputCount → Fin 6) ×
      (Fin outputCount → Fin 6) ×
      (Fin outputCount → Fin 6) ×
      (Fin outputCount → Fin outputCount → Bool) ×
      (Fin outputCount → CorridorPort 2 0 → Bool) where
  toFun code := ⟨code.usesInput, code.residueCap, code.localCap,
    code.overlapCap, code.outputFaceContinues,
    code.outputFragmentContainsPort⟩
  invFun code :=
    { usesInput := code.1
      residueCap := code.2.1
      localCap := code.2.2.1
      overlapCap := code.2.2.2.1
      outputFaceContinues := code.2.2.2.2.1
      outputFragmentContainsPort := code.2.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (inputCount outputCount : Nat) :
    Fintype (BoundedSerialFaceTransitionCode inputCount outputCount) :=
  Fintype.ofEquiv _
    (boundedSerialFaceTransitionCodeEquiv inputCount outputCount).symm

/-- The visible capped contribution from the input profile. -/
def BoundedSerialFaceTransitionCode.selectedInputCap
    {inputCount outputCount : Nat}
    (code : BoundedSerialFaceTransitionCode inputCount outputCount)
    (inputCap : Fin inputCount → Fin 6) (output : Fin outputCount) : Nat :=
  min (∑ input,
    if code.usesInput output input then (inputCap input).val else 0) 5

/-- Decode one outgoing capped face length from the input profile and the
finite literal transition witness. -/
def BoundedSerialFaceTransitionCode.outputCap
    {inputCount outputCount : Nat}
    (code : BoundedSerialFaceTransitionCode inputCount outputCount)
    (inputCap : Fin inputCount → Fin 6) (output : Fin outputCount) : Nat :=
  min
    (min (code.selectedInputCap inputCap output +
        (code.residueCap output).val) 5 +
      (code.localCap output).val - (code.overlapCap output).val)
    5

/-- The complete finite facial relation between two route-correct serial
profiles.  All indices are the profiles' actual dependent fragment
coordinates; no padding or ambient graph carrier occurs. -/
def BoundedSerialFaceTransition
    (input output : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∃ code : BoundedSerialFaceTransitionCode input.faceFragmentCount.val
      output.faceFragmentCount.val,
    (∀ left right,
      output.profile.faceContinues left right =
        code.outputFaceContinues left right) ∧
    (∀ fragment port,
      output.profile.fragmentContainsPort fragment port =
        code.outputFragmentContainsPort fragment port) ∧
    (∀ fragment,
      (output.profile.faceLengthCap fragment).val =
        code.outputCap input.profile.faceLengthCap fragment)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFaceTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Extract all finite facial data of one actual literal serial transition.
The output cap is deliberately omitted from the code; the theorem below
reconstructs it from the other fields and the input profile. -/
noncomputable def sourceCorridorSerialFaceTransitionCodeAt
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
    let input := sourceCorridorSerialInputBoundedProfileAt realization hcubic
      hrotation htwoSided hunique offset color hinputColor
    let output := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
      hrotation htwoSided hunique offset color houtputColor
    BoundedSerialFaceTransitionCode input.faceFragmentCount.val
      output.faceFragmentCount.val := by
  let input := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor
  let output := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color houtputColor
  exact
    { usesInput := fun fragment inputFragment =>
        sourceCorridorSerialInputFaceUsedByOutputBoolAt realization hcubic
          hrotation htwoSided hunique offset fragment inputFragment
      residueCap := fun fragment =>
        sourceCorridorSerialOldFaceInputResidueCapAt realization hcubic
          hrotation htwoSided hunique offset fragment
      localCap := fun fragment => ⟨
        min (sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset fragment).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      overlapCap := fun fragment => ⟨
        min ((sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
            htwoSided hunique offset fragment) ∩
          sourceCorridorSerialLocalFaceSliceAt realization hcubic hrotation
            htwoSided hunique offset fragment).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      outputFaceContinues := output.profile.faceContinues
      outputFragmentContainsPort := output.profile.fragmentContainsPort }

/-- The two graph-derived serial profiles around one literal Cell satisfy the
complete finite facial transition. -/
theorem sourceCorridorSerialBoundedProfiles_faceTransition
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
    BoundedSerialFaceTransition
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hinputColor)
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color houtputColor) := by
  let input := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor
  let output := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color houtputColor
  let code := sourceCorridorSerialFaceTransitionCodeAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor houtputColor
  change BoundedSerialFaceTransition input output
  refine ⟨code, ?_, ?_, ?_⟩
  · intro left right
    rfl
  · intro fragment port
    rfl
  · intro fragment
    convert
      sourceCorridorSerialPrefix_faceLengthCap_eq_profile_residual realization
        hcubic hrotation htwoSided hunique offset color hinputColor
        houtputColor fragment using 1
    all_goals
      simp only [code, input, output,
        sourceCorridorSerialFaceTransitionCodeAt,
        sourceCorridorSerialInputFaceCapAt,
        BoundedSerialFaceTransitionCode.outputCap,
        BoundedSerialFaceTransitionCode.selectedInputCap]
      rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
