import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialFullTransitionExecutable

/-!
# Exact scope of the abstract serial-transition over-approximation

`BoundedSerialFullTransition` was introduced as a source-image relation.  Its
residual tracked and facial fields deliberately permit finite information
which is not determined by the displayed input profile.  This file measures
the resulting abstraction before it is used for a reachable-state count.

For any output whose positive tracked-connectivity bits have the colors they
claim, every input admits an abstract transition to that output.  The proof
stores the output connectivity in `hiddenConnected`, stores each output face
cap in `residueCap`, and uses no input coordinate.  Consequently the existing
executable relation is a sound conservative envelope, but its closure cannot
serve as the desired geometric compression.

This is not a defect in the source profile.  It identifies the exact next
obligation: restrict the finite letters by the literal Cell/rebase receipts,
including their attachment to the incoming profile, before measuring
reachability.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- The minimal validity condition used below: every asserted tracked
connection has endpoint colors belonging to its named color pair.  Actual
graph-derived profiles satisfy this because tracked connectivity is computed
inside the corresponding two-color graph. -/
def BoundedWidthTwoTrackedSound
    (profile : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∀ (pair : TrackedColorPair) (left right : Fin 2),
    profile.profile.strandConnected pair (.inl left) (.inl right) = true →
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (profile.profile.edgeColor left).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (profile.profile.edgeColor right).toColor

/-- An abstract letter which ignores the input and retains every output field
in the unrestricted residual coordinates. -/
def unrestrictedOutputTransitionCode
    (input output : BoundedCorridorCutProfile 2 0 4) :
    BoundedSerialFullTransitionCode input.faceFragmentCount.val
      output.faceFragmentCount.val where
  outputEdgeColor := output.profile.edgeColor
  tracked :=
    { usesInput := fun _ _ _ => false
      hiddenConnected := fun pair left right =>
        output.profile.strandConnected pair (.inl left) (.inl right) }
  face :=
    { usesInput := fun _ _ => false
      residueCap := output.profile.faceLengthCap
      localCap := fun _ => 0
      overlapCap := fun _ => 0
      outputFaceContinues := output.profile.faceContinues
      outputFragmentContainsPort := output.profile.fragmentContainsPort }

/-- The unrestricted face receipt decodes exactly the copied output cap. -/
theorem unrestrictedOutputTransitionCode_outputCap
    (input output : BoundedCorridorCutProfile 2 0 4)
    (fragment : Fin output.faceFragmentCount.val) :
    (unrestrictedOutputTransitionCode input output).face.outputCap
        input.profile.faceLengthCap fragment =
      (output.profile.faceLengthCap fragment).val := by
  simp [unrestrictedOutputTransitionCode,
    BoundedSerialFaceTransitionCode.outputCap,
    BoundedSerialFaceTransitionCode.selectedInputCap]
  omega

/-- The abstract source-image relation is input-independent on every tracked
sound output.  Therefore it must not be used as the compressed geometric
transition without an additional receipt-compatibility predicate. -/
theorem boundedSerialFullTransition_of_trackedSound
    (input output : BoundedCorridorCutProfile 2 0 4)
    (hsound : BoundedWidthTwoTrackedSound output) :
    BoundedSerialFullTransition input output := by
  refine ⟨unrestrictedOutputTransitionCode input output, ?_, ?_, ?_, ?_, ?_⟩
  · intro step
    rfl
  · intro pair left right
    constructor
    · intro hconnected
      exact ⟨(hsound pair left right hconnected).1,
        (hsound pair left right hconnected).2, Or.inl hconnected⟩
    · rintro ⟨_hleft, _hright, hhidden | hvisible⟩
      · exact hhidden
      · rcases hvisible with
          ⟨inputLeft, inputRight, hleft, _hinput, _hright⟩
        simp [unrestrictedOutputTransitionCode] at hleft
  · intro left right
    rfl
  · intro fragment port
    rfl
  · intro fragment
    exact (unrestrictedOutputTransitionCode_outputCap input output fragment).symm

/-- The executable presentation inherits the same scope: some finite letter
decodes every tracked-sound output from every input. -/
theorem exists_fullLetter_decode_eq_some_of_trackedSound
    (input output : BoundedCorridorCutProfile 2 0 4)
    (hsound : BoundedWidthTwoTrackedSound output) :
    ∃ code : BoundedSerialFullLetterCode,
      code.decode input = some output :=
  exists_letter_decode_eq_some_of_fullTransition
    (boundedSerialFullTransition_of_trackedSound input output hsound)

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
