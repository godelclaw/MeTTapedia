import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Basic

/-!
# Admission laws for prepared collection regions

A relational predicate may fail, return several Boolean answers, or perform an
observable effect. A direct filter is equivalent to relational filtering only
when every invoked occurrence has one exact Boolean answer and the predicate is
independently known to be pure. Revision-indexed evidence prevents that fact
from surviving a program change silently.

The fold model separates extensional results from representation cost. Copying
the previous accumulator before every prepend computes the same list as sharing
it, but its accumulated copy count is triangular rather than linear.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedCollectionRegions

universe u v

variable {α : Type u} {ε : Type v}

/-- Relational filtering keeps an occurrence when any answer is `true`. -/
def relationalFilter (answers : α → List Bool) (items : List α) : List α :=
  items.filter fun item => decide (true ∈ answers item)

/-- A prepared filter consumes one already established Boolean per occurrence. -/
def preparedFilter (test : α → Bool) (items : List α) : List α :=
  items.filter test

/-- Exact single-result evidence is joint: it covers every invoked occurrence. -/
def ExactSingleResult (answers : α → List Bool) (test : α → Bool) : Prop :=
  ∀ item, answers item = [test item]

theorem exact_single_result_membership
    (answers : α → List Bool) (test : α → Bool)
    (exact : ExactSingleResult answers test) (item : α) :
    true ∈ answers item ↔ test item = true := by
  rw [exact item]
  cases test item <;> simp

/-- Single-result evidence justifies the direct route while preserving order
and duplicate occurrences exactly. -/
theorem prepared_filter_eq_relational
    (answers : α → List Bool) (test : α → Bool)
    (exact : ExactSingleResult answers test) (items : List α) :
    preparedFilter test items = relationalFilter answers items := by
  apply congrArg (fun predicate : α → Bool => items.filter predicate)
  funext item
  rw [exact item]
  cases test item <;> decide

/-- Classification returns evidence only for one exact Boolean occurrence. -/
def exactBoolean : List Bool → Option Bool
  | [answer] => some answer
  | _ => none

theorem exactBoolean_eq_some_iff (answers : List Bool) (answer : Bool) :
    exactBoolean answers = some answer ↔ answers = [answer] := by
  cases answers with
  | nil => simp [exactBoolean]
  | cons first rest =>
      cases rest with
      | nil => simp [exactBoolean]
      | cons second tail => simp [exactBoolean]

/-- Taking one branch of a multi-answer predicate is not relational filtering. -/
theorem first_answer_is_unsound_for_nondeterminism :
    preparedFilter (fun _ : Nat => false) [0] ≠
      relationalFilter (fun _ : Nat => [false, true]) [0] := by
  decide

/-- Failure to obtain an answer is distinct from a justified `false`. -/
theorem no_answer_is_not_false_evidence :
    exactBoolean [] = none ∧ exactBoolean [false] = some false := by
  decide

/-- Effects are a separate observation from the returned Boolean occurrences. -/
structure PredicateObservation (ε : Type v) where
  answers : List Bool
  trace : List ε
  deriving DecidableEq

def booleanProjection (observation : PredicateObservation ε) : List Bool :=
  observation.answers

/-- Equal Boolean answers cannot establish purity: an effect trace may differ. -/
theorem equal_booleans_can_hide_effects :
    let pure : PredicateObservation Unit := ⟨[true], []⟩
    let writes : PredicateObservation Unit := ⟨[true], [()]⟩
    booleanProjection pure = booleanProjection writes ∧ pure ≠ writes := by
  decide

/-- Evidence records the immutable program revision at which it was proved. -/
structure ClassifierEvidence (α : Type u) where
  revision : Nat
  test : α → Bool

def ValidAt (world : Nat → α → List Bool)
    (evidence : ClassifierEvidence α) (revision : Nat) : Prop :=
  evidence.revision = revision ∧
    ExactSingleResult (world revision) evidence.test

theorem valid_evidence_preserves_filter
    (world : Nat → α → List Bool) (evidence : ClassifierEvidence α)
    (revision : Nat) (valid : ValidAt world evidence revision)
    (items : List α) :
    preparedFilter evidence.test items =
      relationalFilter (world revision) items :=
  prepared_filter_eq_relational _ _ valid.2 _

namespace RevisionControl

def world : Nat → Unit → List Bool
  | 0, _ => [false]
  | _, _ => [true]

def oldEvidence : ClassifierEvidence Unit :=
  ⟨0, fun _ => false⟩

theorem old_evidence_valid_at_zero : ValidAt world oldEvidence 0 := by
  constructor <;> simp [oldEvidence, world, ExactSingleResult]

theorem old_evidence_invalid_at_one : ¬ ValidAt world oldEvidence 1 := by
  simp [ValidAt, oldEvidence]

/-- Reusing the old classifier after the program changes loses an answer. -/
theorem stale_evidence_changes_answer :
    preparedFilter oldEvidence.test [()] ≠ relationalFilter (world 1) [()] := by
  decide

end RevisionControl

/-- The costly model copies the whole prior list before prepending. -/
def rebuildingFold (items : List α) (initial : List α) : List α :=
  items.foldl (fun accumulated item => item :: accumulated.map id) initial

/-- The sharing model prepends while retaining the prior accumulator. -/
def retainingFold (items : List α) (initial : List α) : List α :=
  items.foldl (fun accumulated item => item :: accumulated) initial

/-- Representation choice changes cost without changing the delivered value. -/
theorem rebuilding_fold_eq_retaining_fold
    (items initial : List α) :
    rebuildingFold items initial = retainingFold items initial := by
  simp [rebuildingFold, retainingFold]

theorem retaining_fold_eq_reverse_append (items initial : List α) :
    retainingFold items initial = items.reverse ++ initial := by
  induction items generalizing initial with
  | nil => simp [retainingFold]
  | cons item rest _ =>
      simp [retainingFold, List.reverse_cons, List.append_assoc]

/-- Number of prior cells revisited by rebuilding an initially empty growing
accumulator once at each step. -/
def repeatedCopyCost (steps : Nat) : Nat :=
  ∑ size ∈ Finset.range steps, size

/-- A shared prepend allocates one fresh spine cell per step. -/
def sharedExtensionCost (steps : Nat) : Nat := steps

/-- The repeated-copy cost is exactly triangular. This is an arithmetic cost
law, independent of elapsed time, allocation policy, and cache effects. -/
theorem repeated_copy_cost_twice (steps : Nat) :
    repeatedCopyCost steps * 2 = steps * (steps - 1) := by
  exact Finset.sum_range_id_mul_two steps

theorem shared_extension_cost_linear (steps : Nat) :
    sharedExtensionCost steps = steps := rfl

namespace Controls

theorem duplicate_occurrences_are_preserved :
    preparedFilter (fun n : Nat => n == 1) [1, 1, 2, 1] = [1, 1, 1] := by
  decide

theorem exact_false_is_a_completed_decision :
    exactBoolean [false] = some false := by
  rfl

theorem multiple_equal_answers_still_decline :
    exactBoolean [true, true] = none := by
  rfl

theorem four_step_cost_gap :
    repeatedCopyCost 4 = 6 ∧ sharedExtensionCost 4 = 4 := by
  decide

end Controls

#print axioms prepared_filter_eq_relational
#print axioms RevisionControl.stale_evidence_changes_answer
#print axioms rebuilding_fold_eq_retaining_fold
#print axioms repeated_copy_cost_twice

end Mettapedia.Machines.PreparedCollectionRegions
