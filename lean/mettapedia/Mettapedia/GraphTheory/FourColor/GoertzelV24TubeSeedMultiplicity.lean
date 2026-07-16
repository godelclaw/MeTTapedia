import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityAudit0
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityAudit1
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityAudit2
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityAudit3
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityAudit4

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

open GoertzelV24CorridorPumping

theorem phaseA_fullyRoutedChoice_iff
    (index : Fin 10) (choice : TubeRingChoice) :
    choice.FullyRouted (recurrentPhaseAState index) ↔
      choice = phaseAFirstFullyRoutedChoice index ∨
      choice = phaseASecondFullyRoutedChoice index := by
  fin_cases index <;>
    first
    | exact phaseA0_fullyRoutedChoice_iff choice
    | exact phaseA1_fullyRoutedChoice_iff choice
    | exact phaseA2_fullyRoutedChoice_iff choice
    | exact phaseA3_fullyRoutedChoice_iff choice
    | exact phaseA4_fullyRoutedChoice_iff choice
    | exact phaseA5_fullyRoutedChoice_iff choice
    | exact phaseA6_fullyRoutedChoice_iff choice
    | exact phaseA7_fullyRoutedChoice_iff choice
    | exact phaseA8_fullyRoutedChoice_iff choice
    | exact phaseA9_fullyRoutedChoice_iff choice

theorem phaseB_fullyRoutedChoice_iff
    (index : Fin 10) (choice : TubeRingChoice) :
    choice.FullyRouted (recurrentPhaseBState index) ↔
      choice = phaseBFirstFullyRoutedChoice index ∨
      choice = phaseBSecondFullyRoutedChoice index := by
  fin_cases index <;>
    first
    | exact phaseB0_fullyRoutedChoice_iff choice
    | exact phaseB1_fullyRoutedChoice_iff choice
    | exact phaseB2_fullyRoutedChoice_iff choice
    | exact phaseB3_fullyRoutedChoice_iff choice
    | exact phaseB4_fullyRoutedChoice_iff choice
    | exact phaseB5_fullyRoutedChoice_iff choice
    | exact phaseB6_fullyRoutedChoice_iff choice
    | exact phaseB7_fullyRoutedChoice_iff choice
    | exact phaseB8_fullyRoutedChoice_iff choice
    | exact phaseB9_fullyRoutedChoice_iff choice

/-- Exhaustive classification of the alive column: every recurrent frontier
has exactly the two displayed five-bit fully-routed choices. -/
theorem recurrentProfile_fullyRoutedChoice_iff
    (source : RecurrentTubeProfile) (choice : TubeRingChoice) :
    choice.FullyRouted (recurrentProfileState source) ↔
      choice = firstFullyRoutedChoice source ∨
      choice = secondFullyRoutedChoice source := by
  rcases source with ⟨phase, index⟩
  cases phase with
  | false =>
      simpa [recurrentProfileState, firstFullyRoutedChoice,
        secondFullyRoutedChoice] using phaseA_fullyRoutedChoice_iff index choice
  | true =>
      simpa [recurrentProfileState, firstFullyRoutedChoice,
        secondFullyRoutedChoice] using phaseB_fullyRoutedChoice_iff index choice

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem firstFullyRoutedChoice_isSuccessor :
    ∀ source : RecurrentTubeProfile,
      IsTubeRingSuccessor
        (recurrentProfileState source)
        (recurrentProfileState (firstFullyRoutedTarget source))
        (firstFullyRoutedChoice source) := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem secondFullyRoutedChoice_isSuccessor :
    ∀ source : RecurrentTubeProfile,
      IsTubeRingSuccessor
        (recurrentProfileState source)
        (recurrentProfileState (secondFullyRoutedTarget source))
        (secondFullyRoutedChoice source) := by
  decide

theorem firstFullyRoutedChoice_ne_second :
    ∀ source : RecurrentTubeProfile,
      firstFullyRoutedChoice source ≠ secondFullyRoutedChoice source := by
  decide

/-- The ten middle-edge colors determine all five split choices. Thus the
two audited branches are distinct coloring extensions, not duplicate
certificates for one extension. -/
theorem middleColor_choice_injective (source : TubeFrontierState) :
    Function.Injective (middleColor source) := by
  intro left right hequal
  funext position
  have hedge := congrFun hequal (firstLeft position)
  cases hleft : left position <;> cases hright : right position
  · rfl
  · cases hcolor : source.color position <;>
      simp [middleColor, middleFirst_firstLeft, middleSlot_firstLeft,
        hleft, hright, hcolor, firstComplement, secondComplement] at hedge
  · cases hcolor : source.color position <;>
      simp [middleColor, middleFirst_firstLeft, middleSlot_firstLeft,
        hleft, hright, hcolor, firstComplement, secondComplement] at hedge
  · rfl

/-- The recurrent tables are closed under every computed fully-routed
choice, not merely under one selected witness per source. -/
theorem recurrentProfile_fullyRouted_closed
    (source : RecurrentTubeProfile) (choice : TubeRingChoice)
    (hchoice : choice.FullyRouted (recurrentProfileState source)) :
    ∃ target : RecurrentTubeProfile,
      IsTubeRingSuccessor
        (recurrentProfileState source) (recurrentProfileState target) choice := by
  rcases (recurrentProfile_fullyRoutedChoice_iff source choice).1 hchoice with
    hfirst | hsecond
  · subst choice
    exact ⟨firstFullyRoutedTarget source,
      firstFullyRoutedChoice_isSuccessor source⟩
  · subst choice
    exact ⟨secondFullyRoutedTarget source,
      secondFullyRoutedChoice_isSuccessor source⟩

/-- On a recurrent frontier, the computed fully-routed predicate is exactly
existence of a genuine successor state in the recurrent tables. -/
theorem recurrentProfile_fullyRouted_iff_exists_successor
    (source : RecurrentTubeProfile) (choice : TubeRingChoice) :
    choice.FullyRouted (recurrentProfileState source) ↔
      ∃ target : RecurrentTubeProfile,
        IsTubeRingSuccessor
          (recurrentProfileState source) (recurrentProfileState target) choice := by
  constructor
  · exact recurrentProfile_fullyRouted_closed source choice
  · rintro ⟨target, hsuccessor⟩
    have hterminal := computedRoutedTerminal_eq_of_successor hsuccessor
    change IsFullyRoutedTubeRingChoice (recurrentProfileState source) choice
      (computedRoutedTerminal (recurrentProfileState source) choice)
    rw [hterminal]
    exact isFullyRoutedTubeRingChoice_of_successor hsuccessor

/-- The finite set of all five-bit choices that preserve the four routed
strands from a recurrent frontier state. -/
abbrev FullyRoutedTubeRingChoice (source : RecurrentTubeProfile) :=
  {choice : TubeRingChoice //
    choice.FullyRouted (recurrentProfileState source)}

/-- Every recurrent frontier has exactly two fully-routed one-ring choices.
This is the normalized column audit behind the tube's binary
stay-or-step mechanism. -/
theorem recurrentProfile_fullyRoutedChoice_card
    (source : RecurrentTubeProfile) :
    Fintype.card (FullyRoutedTubeRingChoice source) = 2 := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter
          (fun choice : TubeRingChoice =>
            choice.FullyRouted (recurrentProfileState source)) =
        {firstFullyRoutedChoice source, secondFullyRoutedChoice source} := by
    ext choice
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    exact recurrentProfile_fullyRoutedChoice_iff source choice
  rw [hfilter]
  simp [firstFullyRoutedChoice_ne_second source]

/-- A fully-routed choice has a recurrent successor, selected from the
exhaustive closure theorem. -/
noncomputable def fullyRoutedNextProfile
    (source : RecurrentTubeProfile)
    (choice : FullyRoutedTubeRingChoice source) : RecurrentTubeProfile :=
  Classical.choose
    (recurrentProfile_fullyRouted_closed source choice choice.property)

theorem fullyRoutedNextProfile_isSuccessor
    (source : RecurrentTubeProfile)
    (choice : FullyRoutedTubeRingChoice source) :
    IsTubeRingSuccessor
      (recurrentProfileState source)
      (recurrentProfileState (fullyRoutedNextProfile source choice)) choice :=
  Classical.choose_spec
    (recurrentProfile_fullyRouted_closed source choice choice.property)

/-- Fully-routed histories through a normalized tube. At each ring this type
stores exactly one of the computed alive choices; the next recurrent state is
the genuine successor certified above. -/
def FullyRoutedTubeHistory :
    (rings : Nat) -> RecurrentTubeProfile -> Type
  | 0, _source => Unit
  | rings + 1, source =>
      Σ choice : FullyRoutedTubeRingChoice source,
        FullyRoutedTubeHistory rings
          (fullyRoutedNextProfile source choice)

/-- The ordered five-bit choice made at every ring of a fully-routed
history. -/
noncomputable def FullyRoutedTubeHistory.choiceVector :
    {rings : Nat} -> {source : RecurrentTubeProfile} ->
      FullyRoutedTubeHistory rings source -> Fin rings -> TubeRingChoice
  | 0, _source, _history => Fin.elim0
  | _rings + 1, _source, ⟨choice, tail⟩ =>
      Fin.cases choice tail.choiceVector

/-- Distinct fully-routed histories have distinct ordered ring-choice data. -/
theorem FullyRoutedTubeHistory.choiceVector_injective
    (rings : Nat) (source : RecurrentTubeProfile) :
    Function.Injective
      (@FullyRoutedTubeHistory.choiceVector rings source) := by
  induction rings generalizing source with
  | zero =>
      intro left right _hequal
      cases left
      cases right
      rfl
  | succ rings ih =>
      rintro ⟨leftChoice, leftTail⟩ ⟨rightChoice, rightTail⟩ hequal
      have hchoice : leftChoice = rightChoice := by
        apply Subtype.ext
        simpa [FullyRoutedTubeHistory.choiceVector] using
          congrFun hequal (0 : Fin (rings + 1))
      subst rightChoice
      have htail : leftTail.choiceVector = rightTail.choiceVector := by
        funext ring
        simpa [FullyRoutedTubeHistory.choiceVector] using
          congrFun hequal ring.succ
      have := ih (fullyRoutedNextProfile source leftChoice) htail
      subst rightTail
      rfl

noncomputable instance fullyRoutedTubeHistoryFintype
    (rings : Nat) (source : RecurrentTubeProfile) :
    Fintype (FullyRoutedTubeHistory rings source) := by
  induction rings generalizing source with
  | zero =>
      change Fintype Unit
      infer_instance
  | succ rings ih =>
      change Fintype
        (Σ choice : FullyRoutedTubeRingChoice source,
          FullyRoutedTubeHistory rings
            (fullyRoutedNextProfile source choice))
      letI (choice : FullyRoutedTubeRingChoice source) :
          Fintype (FullyRoutedTubeHistory rings
            (fullyRoutedNextProfile source choice)) := ih _
      infer_instance

/-- Exact doubling of the fully-routed history mass at every normalized ring
extension. -/
theorem fullyRoutedTubeHistory_card :
    ∀ rings source,
      Fintype.card (FullyRoutedTubeHistory rings source) = 2 ^ rings := by
  intro rings
  induction rings with
  | zero =>
      intro source
      simp [FullyRoutedTubeHistory]
  | succ rings ih =>
      intro source
      change Fintype.card
          (Σ choice : FullyRoutedTubeRingChoice source,
            FullyRoutedTubeHistory rings
              (fullyRoutedNextProfile source choice)) = _
      rw [Fintype.card_sigma]
      simp_rw [ih]
      rw [Finset.sum_const, Finset.card_univ,
        recurrentProfile_fullyRoutedChoice_card]
      simp [pow_succ, Nat.mul_comm]

/-- Endpoint and genuine transfer proof assembled from a fully-routed
history. -/
structure FullyRoutedTubeTransfer
    (rings : Nat) (source : RecurrentTubeProfile) where
  target : RecurrentTubeProfile
  transfer : ExactRelationalTransfer TubeRingStep rings
    (recurrentProfileState source) (recurrentProfileState target)

/-- A fully-routed history is an exact path of genuine one-ring transfers. -/
noncomputable def FullyRoutedTubeHistory.toExactTransfer :
    {rings : Nat} -> {source : RecurrentTubeProfile} ->
      (history : FullyRoutedTubeHistory rings source) ->
      FullyRoutedTubeTransfer rings source
  | 0, source, _history =>
      ⟨source, .zero (recurrentProfileState source)⟩
  | _rings + 1, source, ⟨choice, tail⟩ =>
      let tailTransfer := toExactTransfer tail
      ⟨tailTransfer.target, .succ
        ⟨choice, fullyRoutedNextProfile_isSuccessor source choice⟩
        tailTransfer.transfer⟩

/-- A history assembles into a genuine corridor certificate with shared
frontier states and locally Tait-valid ring choices. -/
noncomputable def FullyRoutedTubeHistory.toTaitColoring
    {rings : Nat} {source : RecurrentTubeProfile}
    (history : FullyRoutedTubeHistory rings source) :
    Σ target : RecurrentTubeProfile,
      TubeCorridorTaitColoring rings
        (recurrentProfileState source) (recurrentProfileState target) :=
  ⟨history.toExactTransfer.target,
    Classical.choice
      (exactTransfer_exists_taitColoring history.toExactTransfer.transfer)⟩

theorem FullyRoutedTubeHistory.toTaitColoring_locallyTait
    {rings : Nat} {source : RecurrentTubeProfile}
    (history : FullyRoutedTubeHistory rings source) :
    history.toTaitColoring.2.LocallyTait :=
  history.toTaitColoring.2.locallyTait

/-- With manuscript tube index `j >= 1`, the corridor contains `j+1`
normalized ring extensions. The exact history mass is therefore the stated
`4 * 2^(j-1)`. -/
theorem fullyRoutedTubeSeed_mass
    (j : Nat) (hj : 1 <= j) (source : RecurrentTubeProfile) :
    Fintype.card (FullyRoutedTubeHistory (j + 1) source) =
      4 * 2 ^ (j - 1) := by
  rw [fullyRoutedTubeHistory_card]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k + 1 = k + 2 by omega]
  simp only [Nat.add_sub_cancel_left]
  rw [pow_succ, pow_succ]
  ring

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
