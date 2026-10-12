import Mettapedia.GSLT.Causality.LocatedFundingCompleteness
import Mettapedia.GSLT.Causality.LocatedPermittedProjectionControls

/-!
# Ordered funding distinguishes complete histories with the same endpoint

The two actual receives commute in the original resource system. A single
purse with different successive keys funds precisely the declared first
order. The reverse order has the same endpoint, number of firings and bag
of required keys, but cannot use that purse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.LocatedFundingCompletenessControls

open OccurrenceHistory Controls LocatedHistoryControls LocatedProjectionControls

def originalKey : ∀ {site : persistentReceiver.Site}, persistentReceiver.Instance site → Bool :=
  fun {_site} => fun firing : Nat => decide (firing = 1)

def orderedSystem : System (Res ⊕ (Nat × List Bool)) :=
  locatedPermitted persistentReceiver permitted (fun _ => 0) @originalKey

def orderedPick (value : Nat) (permission : value = 1 ∨ value = 2) (tail : List Bool) :
    orderedSystem.Instance () := (⟨value, permission⟩, tail)

def firstWord : List orderedSystem.Entry :=
  [⟨(), orderedPick 1 (Or.inl rfl) [false]⟩, ⟨(), orderedPick 2 (Or.inr rfl) []⟩]

def reverseWord : List orderedSystem.Entry :=
  [⟨(), orderedPick 2 (Or.inr rfl) [true]⟩, ⟨(), orderedPick 1 (Or.inl rfl) []⟩]

def orderedPurse : Multiset (Nat × List Bool) := {(0, [true, false])}

def exhaustedPurse : Multiset (Nat × List Bool) := {(0, [])}

theorem first_word_reads_original :
    firstWord.map (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) @originalKey) =
      persistentReceiver.pathEntries firstOriginal := by
  rw [first_projection_retains_the_complete_order]
  rfl

theorem reverse_word_reads_original :
    reverseWord.map (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) @originalKey) =
      persistentReceiver.pathEntries secondOriginal := by
  rw [second_projection_retains_the_complete_order]
  rfl

theorem actual_purse_plan :
    (pursesMany Nat Bool).Fires
      (firstWord.map (locatedPurseEntry persistentReceiver permitted (fun _ => 0) @originalKey))
        orderedPurse exhaustedPurse := by
  change (pursesMany Nat Bool).Fires
    [⟨(0 : Nat), ({(true, [false])} : Multiset (Bool × List Bool))⟩,
      ⟨(0 : Nat), ({(false, [])} : Multiset (Bool × List Bool))⟩]
        {(0, [true, false])} {(0, [])}
  simp only [System.Fires, System.Enables, System.fire, pursesMany]
  decide

theorem specified_order_is_actually_funded :
    ∃ paid : OccurrencePath orderedSystem.presentation
      (marking (leftPart start) orderedPurse) (marking (leftPart finish) exhaustedPurse),
      orderedSystem.pathEntries paid = firstWord ∧
        HEq (locatedOriginalPath persistentReceiver permitted (fun _ => 0) @originalKey paid)
          firstOriginal :=
  (specified_history_has_located_funding_iff persistentReceiver permitted
    (fun _ => 0) @originalKey firstOriginal firstWord first_word_reads_original
      orderedPurse exhaustedPurse).mpr actual_purse_plan

theorem reverse_purse_plan_rejected :
    ¬ (pursesMany Nat Bool).Fires
      (reverseWord.map (locatedPurseEntry persistentReceiver permitted (fun _ => 0) @originalKey))
        orderedPurse exhaustedPurse := by
  change ¬ (pursesMany Nat Bool).Fires
    [⟨(0 : Nat), ({(false, [true])} : Multiset (Bool × List Bool))⟩,
      ⟨(0 : Nat), ({(true, [])} : Multiset (Bool × List Bool))⟩]
        {(0, [true, false])} {(0, [])}
  simp only [System.Fires, System.Enables, System.fire, pursesMany]
  decide

theorem reverse_order_has_no_paid_history :
    ¬ ∃ paid : OccurrencePath orderedSystem.presentation
      (marking (leftPart start) orderedPurse) (marking (leftPart finish) exhaustedPurse),
        (orderedSystem.pathEntries paid).map
          (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) @originalKey) =
            persistentReceiver.pathEntries secondOriginal := by
  rintro ⟨paid, readings⟩
  rw [second_projection_retains_the_complete_order] at readings
  have executes := orderedSystem.fires_pathEntries paid
  generalize wordEq : orderedSystem.pathEntries paid = word at readings executes
  cases word with
  | nil => cases readings
  | cons entry rest =>
      have firstReading := (List.cons.inj readings).1
      have value : entry.2.1.val = (2 : Nat) :=
        congrArg (fun entry : persistentReceiver.Entry => (entry.2 : Nat)) firstReading
      have enabled : orderedSystem.Enables (marking (leftPart start) orderedPurse)
          entry.2 := executes.1
      have present := ((locatedPermitted_enables_iff persistentReceiver permitted
        (fun _ => 0) @originalKey (leftPart start) orderedPurse
          entry.2.1 entry.2.2).mp
            enabled).2
      have wrongKey : originalKey entry.2.1.val = false := by rw [value]; rfl
      change (((0 : Nat), originalKey entry.2.1.val :: entry.2.2) : Nat × List Bool) ∈
        orderedPurse at present
      rw [wrongKey] at present
      have impossible : ¬ ((0, false :: entry.2.2) : Nat × List Bool) ∈ orderedPurse := by
        simp only [orderedPurse, Multiset.mem_singleton, Prod.mk.injEq, List.cons.injEq,
          Bool.false_eq_true, false_and, and_false, not_false_eq_true]
      exact impossible present

theorem same_aggregates_different_funding :
    (persistentReceiver.pathEntries firstOriginal).length =
        (persistentReceiver.pathEntries secondOriginal).length ∧
      ((persistentReceiver.pathEntries firstOriginal).map
          (fun entry => originalKey entry.2) : Multiset Bool) =
        ((persistentReceiver.pathEntries secondOriginal).map
          (fun entry => originalKey entry.2) : Multiset Bool) ∧
      (∃ paid : OccurrencePath orderedSystem.presentation
        (marking (leftPart start) orderedPurse) (marking (leftPart finish) exhaustedPurse),
        orderedSystem.pathEntries paid = firstWord ∧
          HEq (locatedOriginalPath persistentReceiver permitted (fun _ => 0) @originalKey paid)
            firstOriginal) ∧
      ¬ ∃ paid : OccurrencePath orderedSystem.presentation
        (marking (leftPart start) orderedPurse) (marking (leftPart finish) exhaustedPurse),
          (orderedSystem.pathEntries paid).map
            (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) @originalKey) =
              persistentReceiver.pathEntries secondOriginal := by
  refine ⟨?_, ?_, specified_order_is_actually_funded, reverse_order_has_no_paid_history⟩
  · rw [first_projection_retains_the_complete_order, second_projection_retains_the_complete_order]
    rfl
  · rw [first_projection_retains_the_complete_order, second_projection_retains_the_complete_order]
    decide

end Mettapedia.GSLT.Causality.ResourceInteraction.LocatedFundingCompletenessControls
