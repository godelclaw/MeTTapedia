import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorLineGraph

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

open GoertzelV24CorridorPumping

/-- Every state in the certified recurrent subsystem satisfies the exact
four-terminal frontier invariant. -/
theorem recurrentProfileState_valid (profile : RecurrentTubeProfile) :
    (recurrentProfileState profile).Valid := by
  obtain ⟨choice, hsuccessor⟩ :=
    selectedRecurrentSuccessor_isTubeRingStep profile
  exact hsuccessor.1

/-- The recurrent frontier profile after a prescribed number of selected
genuine ring extensions. -/
def recurrentProfileAfter (rings : Nat) (profile : RecurrentTubeProfile) :
    RecurrentTubeProfile :=
  (selectedRecurrentSuccessor^[rings]) profile

/-- The selected successor table realizes a genuine exact transfer path at
every length, not only at return lengths. -/
theorem recurrentProfile_exactTransfer
    (profile : RecurrentTubeProfile) :
    ∀ rings : Nat,
      ExactRelationalTransfer TubeRingStep rings
        (recurrentProfileState profile)
        (recurrentProfileState (recurrentProfileAfter rings profile)) := by
  intro rings
  induction rings generalizing profile with
  | zero =>
      exact .zero (recurrentProfileState profile)
  | succ rings ih =>
      have hstep := selectedRecurrentSuccessor_isTubeRingStep profile
      have htail := ih (selectedRecurrentSuccessor profile)
      have hpath := ExactRelationalTransfer.succ hstep htail
      simpa [recurrentProfileAfter, Function.iterate_succ_apply] using hpath

/-- Recurrent coordinate of the reflected good cap word. -/
def normalizedTubeInitialProfile : RecurrentTubeProfile :=
  (true, (5 : Fin 10))

@[simp]
theorem recurrentProfileState_normalizedTubeInitialProfile :
    recurrentProfileState normalizedTubeInitialProfile = normalizedTubeSeed :=
  rfl

/-- The explicit live output frontier reached after `rings` extensions. -/
def normalizedTubeStateAfter (rings : Nat) : TubeFrontierState :=
  recurrentProfileState (recurrentProfileAfter rings normalizedTubeInitialProfile)

/-- The normalized good seed has a genuine transfer path of every natural
length. -/
theorem normalizedTubeSeed_exactTransfer_everyLength (rings : Nat) :
    ExactRelationalTransfer TubeRingStep rings
      normalizedTubeSeed (normalizedTubeStateAfter rings) := by
  simpa [normalizedTubeStateAfter] using
    recurrentProfile_exactTransfer normalizedTubeInitialProfile rings

theorem normalizedTubeStateAfter_valid (rings : Nat) :
    (normalizedTubeStateAfter rings).Valid :=
  recurrentProfileState_valid _

/-- Every normalized `(5,0)` tube length admits a proper assembled coloring
whose four seed terminals survive in four distinct tracked components. This
is the existence content of the Tube Seed theorem; it does not assert the
separate coloring-multiplicity formula. -/
theorem normalizedTubeSeed_everyLengthFourStrandTaitCorridor
    (rings : Nat) :
    ∃ coloring : TubeCorridorTaitColoring rings
        normalizedTubeSeed (normalizedTubeStateAfter rings),
      coloring.LocallyTait ∧
      ∀ left right : Fin 4,
        coloring.trackedGraph.Reachable
            (.inl (0, normalizedTubeSeed.terminal left))
            (.inl (Fin.last rings,
              (normalizedTubeStateAfter rings).terminal right)) ↔
          left = right := by
  obtain ⟨coloring, hTait⟩ := exactTransfer_exists_locallyTaitColoring
    (normalizedTubeSeed_exactTransfer_everyLength rings)
  exact ⟨coloring, hTait, fun left right =>
    coloring.terminal_reachable_iff normalizedTubeSeed_valid
      (normalizedTubeStateAfter_valid rings) left right⟩

/-- Tube Seed theorem in the original good-cap boundary data, transported by
the proved reflection into normalized ring coordinates. -/
theorem goodTubeCap_everyLengthFourStrandTaitCorridor
    (rings : Nat) :
    ∃ coloring : TubeCorridorTaitColoring rings
        (goodTubeCapState.reindex goodTubeCapReflection)
        (normalizedTubeStateAfter rings),
      coloring.LocallyTait ∧
      ∀ left right : Fin 4,
        coloring.trackedGraph.Reachable
            (.inl (0,
              (goodTubeCapState.reindex goodTubeCapReflection).terminal left))
            (.inl (Fin.last rings,
              (normalizedTubeStateAfter rings).terminal right)) ↔
          left = right := by
  rw [goodTubeCapState_reindex_eq_normalizedTubeSeed]
  exact normalizedTubeSeed_everyLengthFourStrandTaitCorridor rings

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
