import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialFullTransition

/-!
# An executable over-approximation of the literal serial transition

The finite source-image witness is useful for a reachable-state calculation
only after it can be applied without referring back to an ambient graph.  This
file bundles the dependent input and output fragment counts into one finite
letter and gives a deterministic decoder from an input profile to its output.

Every literal source transition is decoded by some such letter.  The converse
is deliberately not asserted: allowing every abstract letter may add spurious
steps.  Consequently the decoder supplies a sound finite over-approximation,
not yet an exact support relation or a claim that its reachable closure is
small.
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

/-- A full finite letter with its dependent fragment counts packaged as
data. -/
structure BoundedSerialFullLetterCode where
  inputCount : Fin 5
  outputCount : Fin 5
  transition : BoundedSerialFullTransitionCode inputCount.val outputCount.val

noncomputable instance : DecidableEq BoundedSerialFullLetterCode :=
  Classical.decEq _

private def boundedSerialFullLetterCodeEquiv :
    BoundedSerialFullLetterCode ≃
      Σ inputCount : Fin 5, Σ outputCount : Fin 5,
        BoundedSerialFullTransitionCode inputCount.val outputCount.val where
  toFun code := ⟨code.inputCount, code.outputCount, code.transition⟩
  invFun code :=
    { inputCount := code.1
      outputCount := code.2.1
      transition := code.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype BoundedSerialFullLetterCode :=
  Fintype.ofEquiv _ boundedSerialFullLetterCodeEquiv.symm

/-- The input cap table reindexed along the count equality checked by the
decoder. -/
def BoundedSerialFullLetterCode.inputFaceLengthCap
    (code : BoundedSerialFullLetterCode)
    (input : BoundedCorridorCutProfile 2 0 4)
    (hcount : input.faceFragmentCount.val = code.inputCount.val) :
    Fin code.inputCount.val → Fin 6 :=
  fun fragment =>
    input.profile.faceLengthCap (Fin.cast hcount.symm fragment)

/-- Boolean tracked-connectivity output computed solely from an incoming
profile and a finite letter. -/
def BoundedSerialFullLetterCode.outputStrandConnected
    (code : BoundedSerialFullLetterCode)
    (input : BoundedCorridorCutProfile 2 0 4)
    (pair : TrackedColorPair) (left right : Fin 2) : Bool :=
  decide
    (IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (code.transition.outputEdgeColor left).toColor ∧
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (code.transition.outputEdgeColor right).toColor ∧
      (code.transition.tracked.hiddenConnected pair left right = true ∨
        ∃ inputLeft inputRight : Fin 2,
          code.transition.tracked.usesInput pair left inputLeft = true ∧
            input.profile.strandConnected pair
                (.inl inputLeft) (.inl inputRight) = true ∧
            code.transition.tracked.usesInput pair right inputRight = true))

/-- The complete graph-free output profile computed by one count-compatible
finite letter. -/
def BoundedSerialFullLetterCode.outputProfile
    (code : BoundedSerialFullLetterCode)
    (input : BoundedCorridorCutProfile 2 0 4)
    (hcount : input.faceFragmentCount.val = code.inputCount.val) :
    BoundedCorridorCutProfile 2 0 4 where
  faceFragmentCount := code.outputCount
  profile :=
    { edgeColor := code.transition.outputEdgeColor
      strandConnected := fun pair left right =>
        match left, right with
        | .inl left, .inl right =>
            code.outputStrandConnected input pair left right
        | .inr terminal, _ => Fin.elim0 terminal
        | _, .inr terminal => Fin.elim0 terminal
      faceContinues := code.transition.face.outputFaceContinues
      fragmentContainsPort :=
        code.transition.face.outputFragmentContainsPort
      faceLengthCap := fun fragment => ⟨
        code.transition.face.outputCap
          (code.inputFaceLengthCap input hcount) fragment,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- Apply a finite letter when its stored input count agrees with the input
profile. -/
def BoundedSerialFullLetterCode.decode
    (code : BoundedSerialFullLetterCode)
    (input : BoundedCorridorCutProfile 2 0 4) :
    Option (BoundedCorridorCutProfile 2 0 4) :=
  if hcount : input.faceFragmentCount.val = code.inputCount.val then
    some (code.outputProfile input hcount)
  else
    none

/-- Every transition admitted by the joint finite source-image relation is
the deterministic output of one packaged finite letter. -/
theorem exists_letter_decode_eq_some_of_fullTransition
    {input output : BoundedCorridorCutProfile 2 0 4}
    (htransition : BoundedSerialFullTransition input output) :
    ∃ code : BoundedSerialFullLetterCode,
      code.decode input = some output := by
  rcases htransition with
    ⟨transition, hedge, hstrand, hface, hport, hcap⟩
  let code : BoundedSerialFullLetterCode :=
    { inputCount := input.faceFragmentCount
      outputCount := output.faceFragmentCount
      transition := transition }
  refine ⟨code, ?_⟩
  rw [BoundedSerialFullLetterCode.decode,
    dif_pos (by simp [code])]
  apply congrArg some
  simp only [code, BoundedSerialFullLetterCode.outputProfile]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext step
    exact (hedge step).symm
  · funext pair left right
    rcases left with left | terminal
    · rcases right with right | terminal
      · change code.outputStrandConnected input pair left right =
          output.profile.strandConnected pair (.inl left) (.inl right)
        apply Bool.eq_iff_iff.mpr
        simp only [BoundedSerialFullLetterCode.outputStrandConnected,
          decide_eq_true_eq, code]
        rw [← hedge left, ← hedge right]
        exact (hstrand pair left right).symm
      · exact Fin.elim0 terminal
    · exact Fin.elim0 terminal
  · funext left right
    exact (hface left right).symm
  · funext fragment port
    exact (hport fragment port).symm
  · funext fragment
    apply Fin.ext
    change transition.face.outputCap input.profile.faceLengthCap fragment =
      (output.profile.faceLengthCap fragment).val
    exact (hcap fragment).symm

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFullTransitionDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every literal source Cell is one step of the graph-free finite decoder.
This is the soundness direction required by any later over-approximate
reachable-closure certificate. -/
theorem exists_fullLetter_decode_sourceCorridorSerialBoundedProfiles
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
    ∃ code : BoundedSerialFullLetterCode,
      code.decode
          (sourceCorridorSerialInputBoundedProfileAt realization hcubic
            hrotation htwoSided hunique offset color hinputColor) =
        some (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
          hrotation htwoSided hunique offset color houtputColor) := by
  apply exists_letter_decode_eq_some_of_fullTransition
  exact sourceCorridorSerialBoundedProfiles_fullTransition realization
    hcubic hrotation htwoSided hunique offset color hinputColor houtputColor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
