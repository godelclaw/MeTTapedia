import Mettapedia.GSLT.Logic.FiniteDepthHennessyMilnerCharacteristic
import Mettapedia.GSLT.Logic.HennessyMilnerBehavioralCoverControls

/-!
# Infinite branching and the actual-label boundary

The positive consumer has infinitely many distinct successors, observable
parity and alarms. Complete finite-depth adequacy applies to its original
steps and equality equations.

The negative consumer has infinitely many labels. One root offers every
finite enabled prefix together with an all-enabled state; the other offers
exactly the finite prefixes. Every finitary formula agrees at the roots,
yet two-round matching fails. The shared finite alternatives are retained,
so negation does not create a spurious one-sided comparison.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner.FiniteDepth.Controls

namespace InfiniteBranching

open BehavioralCoverControls

instance observation_finite : Finite Observation := by
  let : Fintype Observation := Fintype.ofList [.odd, .alarm] (by intro atom; cases atom <;> simp)
  infer_instance

instance system_atoms_finite : Finite system.Atom := observation_finite

instance system_labels_finite : Finite system.Label := by
  change Finite Unit
  infer_instance

theorem complete_depth_adequacy (depth : Nat) (first second : State) :
    FiniteDepth.LogicallyEquivalent system depth first second ↔ Rounds system depth first second :=
  logicallyEquivalent_iff_rounds system depth first second

theorem original_successors_remain_infinite :
    Set.Infinite {target | system.act () (.branch false) target} :=
  literal_successors_are_infinite

theorem depth_zero_cannot_observe_an_enabled_step :
    Rounds system 0 (.branch false) (.terminal 0) := by
  intro atom
  cases atom <;> simp [system, observes]

theorem depth_one_observes_the_step : ¬Rounds system 1 (.branch false) (.terminal 0) := by
  intro related
  obtain ⟨matched, impossible, _⟩ := related.2.1 () (.terminal 0) (Step.branch false 0)
  cases impossible

theorem distinct_parities_separate_at_depth_zero :
    ¬Rounds system 0 (.terminal 0) (.terminal 1) := by
  intro related
  have impossible := (related .odd).mpr rfl
  exact Nat.zero_ne_one impossible

theorem distinct_branches_agree_at_every_depth (depth : Nat) :
    State.branch false ≠ .branch true ∧ Rounds system depth (.branch false) (.branch true) :=
  ⟨by decide, rounds_of_bisimilar system depth (bisimilar_of_kind_eq rfl)⟩

end InfiniteBranching

namespace InfiniteLabels

inductive State where
  | wide
  | narrow
  | allEnabled
  | finiteEnabled (bound : Nat)
  | sink
  deriving DecidableEq

inductive Step : Nat → State → State → Prop
  | wideFinite (bound : Nat) : Step 0 .wide (.finiteEnabled bound)
  | wideAll : Step 0 .wide .allEnabled
  | narrowFinite (bound : Nat) : Step 0 .narrow (.finiteEnabled bound)
  | all (label : Nat) : Step label .allEnabled .sink
  | finite (label bound : Nat) (enabled : label < bound) : Step label (.finiteEnabled bound) .sink

def theory : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites first second := ∃ label, Step label first second
  rewrites_resp_left := by
    rintro first _ second rfl actual
    exact ⟨second, actual, rfl⟩
  rewrites_resp_right := by
    rintro first second _ actual rfl
    exact actual

def system : HennessyMilner.System theory where
  Atom := Empty
  observes atom _ := nomatch atom
  observes_resp := by intro atom; cases atom
  Label := Nat
  act := Step
  act_resp_left := by
    rintro label first _ target rfl actual
    exact ⟨target, actual, rfl⟩
  act_resp_right := by
    rintro label first target _ actual rfl
    exact actual

def maxLabel : Formula Empty Nat → Nat
  | .top => 0
  | .atom atom => nomatch atom
  | .conj first second => max (maxLabel first) (maxLabel second)
  | .neg inner => maxLabel inner
  | .dia label inner => max label (maxLabel inner)

theorem bounded_enabled_agreement (formula : Formula Empty Nat) :
    ∀ bound : Nat, maxLabel formula < bound →
      (system.sat formula .allEnabled ↔ system.sat formula (.finiteEnabled bound)) := by
  induction formula with
  | top => intro bound bounded; exact Iff.rfl
  | atom atom => cases atom
  | conj first second firstRead secondRead =>
      intro bound bounded
      exact and_congr
        (firstRead bound (lt_of_le_of_lt (Nat.le_max_left _ _) bounded))
        (secondRead bound (lt_of_le_of_lt (Nat.le_max_right _ _) bounded))
  | neg inner inductionHypothesis =>
      intro bound bounded
      exact not_congr (inductionHypothesis bound bounded)
  | dia label inner =>
      intro bound bounded
      have enabled : label < bound := lt_of_le_of_lt (Nat.le_max_left _ _) bounded
      constructor
      · rintro ⟨target, actual, held⟩
        cases actual with
        | all => exact ⟨.sink, Step.finite label bound enabled, held⟩
      · rintro ⟨target, actual, held⟩
        cases actual with
        | finite => exact ⟨.sink, Step.all label, held⟩

theorem roots_agree_on_every_finitary_formula :
    system.LogicallyEquivalent .wide .narrow := by
  intro formula
  induction formula with
  | top => exact Iff.rfl
  | atom atom => cases atom
  | conj first second firstRead secondRead => exact and_congr firstRead secondRead
  | neg inner inductionHypothesis => exact not_congr inductionHypothesis
  | dia label inner =>
      constructor
      · rintro ⟨target, actual, held⟩
        cases actual with
        | wideFinite bound => exact ⟨.finiteEnabled bound, Step.narrowFinite bound, held⟩
        | wideAll =>
            exact ⟨.finiteEnabled (maxLabel inner + 1), Step.narrowFinite _,
              (bounded_enabled_agreement inner _ (Nat.lt_succ_self _)).mp held⟩
      · rintro ⟨target, actual, held⟩
        cases actual with
        | narrowFinite bound => exact ⟨.finiteEnabled bound, Step.wideFinite bound, held⟩

theorem roots_agree_at_every_modal_depth (depth : Nat) :
    FiniteDepth.LogicallyEquivalent system depth .wide .narrow :=
  fun formula _ => roots_agree_on_every_finitary_formula formula

theorem roots_fail_two_round_matching : ¬Rounds system 2 .wide .narrow := by
  intro related
  obtain ⟨matched, actual, successors⟩ := related.2.1 (0 : Nat) .allEnabled Step.wideAll
  cases actual with
  | narrowFinite bound =>
      obtain ⟨target, impossible, _⟩ := successors.2.1 bound .sink (Step.all bound)
      cases impossible with
      | finite label bound enabled => exact (Nat.lt_irrefl bound) enabled

theorem actual_label_finiteness_cannot_be_dropped :
    FiniteDepth.LogicallyEquivalent system 2 .wide .narrow ∧ ¬Rounds system 2 .wide .narrow :=
  ⟨roots_agree_at_every_modal_depth 2, roots_fail_two_round_matching⟩

theorem roots_are_not_bisimilar : ¬system.Bisimilar .wide .narrow := by
  intro related
  exact roots_fail_two_round_matching (rounds_of_bisimilar system 2 related)

end InfiniteLabels

end Mettapedia.GSLT.HennessyMilner.FiniteDepth.Controls
