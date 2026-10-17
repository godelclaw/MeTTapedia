import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption

/-!
# Completed cardinality consumers of weighted retained execution

The same physical leaves carry coefficients and answer multiplicity. A complete
cut admits a single-result representation precisely when it contains at most one
returned occurrence and no pending state. The consumer never executes a source
instruction, probes for another answer, or deletes a zero-weight occurrence.

These are representation and resumption laws for an already computed cut. They
do not infer a call-mode contract, prove termination, license early pruning or
reordering, or turn a user annotation into an optimization certificate. Whole
worlds, effects, faults and rights must inhabit the source's retained state and
answer types, with their actual operational correspondence proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedBranchingCardinality

open WeightedResumption WeightedBranchingResumption
open Mettapedia.Machines.AnswerCardinality

variable {State Answer V : Type*}

/-- Failure is a closed empty result. An open cut or several occurrences is
refused; its caller retains the original cut for the general execution path. -/
def singleResult? (leaves : Contributions (Answer ⊕ State) V) :
    Option (Option (Answer × V)) :=
  match leaves with
  | [] => some none
  | [(.inl answer, coefficient)] => some (some (answer, coefficient))
  | _ => none

/-- The complete original cut is recoverable from every accepted reply.
This is equality of ordered occurrences and coefficients, not a value-set law. -/
theorem singleResult_iff (leaves : Contributions (Answer ⊕ State) V)
    (reply : Option (Answer × V)) :
    singleResult? leaves = some reply ↔
      leaves = reply.toList.map (fun item => (.inl item.1, item.2)) := by
  cases leaves with
  | nil => cases reply <;> simp [singleResult?]
  | cons head tail =>
      rcases head with ⟨leaf, coefficient⟩
      cases leaf with
      | inl answer =>
          cases tail with
          | nil =>
              cases reply with
              | none => simp [singleResult?]
              | some item => cases item; simp [singleResult?]
          | cons next rest => cases reply <;> simp [singleResult?]
      | inr pending => cases reply <;> simp [singleResult?]

theorem singleResult_closed (leaves : Contributions (Answer ⊕ State) V)
    (reply : Option (Answer × V)) (accepted : singleResult? leaves = some reply) :
    leaves.all (fun leaf => leaf.1.isLeft) = true := by
  rw [(singleResult_iff leaves reply).mp accepted]
  cases reply <;> rfl

theorem singleResult_cardinality (leaves : Contributions (Answer ⊕ State) V)
    (reply : Option (Answer × V)) (accepted : singleResult? leaves = some reply) :
    Allows .optional (returnedContributions leaves).length := by
  rw [(singleResult_iff leaves reply).mp accepted]
  cases reply <;> simp [Allows, returnedContributions]

/-- Exactly-one admission requires a value reply. Empty closure is semidet. -/
theorem singleResult_item_iff (leaves : Contributions (Answer ⊕ State) V)
    (item : Answer × V) :
    singleResult? leaves = some (some item) ↔ leaves = [(.inl item.1, item.2)] :=
  singleResult_iff leaves (some item)

/-- Admission requires both complete closure and the upper bound. Neither
requirement can be replaced by the cardinality of the returned prefix. -/
theorem singleResult_exists_iff (leaves : Contributions (Answer ⊕ State) V) :
    (∃ reply, singleResult? leaves = some reply) ↔
      leaves.all (fun leaf => leaf.1.isLeft) = true ∧ Allows .optional leaves.length := by
  cases leaves with
  | nil => simp [singleResult?, Allows]
  | cons head tail =>
      rcases head with ⟨leaf, coefficient⟩
      cases tail with
      | nil => cases leaf <;> simp [singleResult?, Allows]
      | cons next rest => simp [singleResult?, Allows]

/-- Choosing the general path returns its complete input cut. The caller
does not have to restart the producer to recover refused alternatives. -/
abbrev Representation (State Answer V : Type*) :=
  Option (Answer × V) ⊕ Contributions (Answer ⊕ State) V

def chooseRepresentation (leaves : Contributions (Answer ⊕ State) V) :
    Representation State Answer V :=
  match singleResult? leaves with
  | some reply => .inl reply
  | none => .inr leaves

def restoreRepresentation : Representation State Answer V → Contributions (Answer ⊕ State) V
  | .inl reply => reply.toList.map (fun item => (.inl item.1, item.2))
  | .inr leaves => leaves

/-- Both accepted and refused representations recover all original state,
answers, coefficients, order and multiplicity. -/
theorem restore_chooseRepresentation (leaves : Contributions (Answer ⊕ State) V) :
    restoreRepresentation (chooseRepresentation leaves) = leaves := by
  unfold chooseRepresentation
  cases checked : singleResult? leaves with
  | none => rfl
  | some reply => exact ((singleResult_iff leaves reply).mp checked).symm

theorem chooseRepresentation_refusal (leaves : Contributions (Answer ⊕ State) V)
    (refused : singleResult? leaves = none) :
    chooseRepresentation leaves = .inr leaves := by
  simp [chooseRepresentation, refused]

/-- Continue the restored owned cut rather than replaying its initial state. -/
def continueRepresentation [Monoid V] (source : Coalgebra State Answer V)
    (fuel : Nat) (representation : Representation State Answer V) :
    Contributions (Answer ⊕ State) V :=
  WeightedResumption.sequence (restoreRepresentation representation) fun leaf =>
    match leaf with
    | .inl answer => [(.inl answer, 1)]
    | .inr pending => contributions source fuel pending

theorem continue_chosen_representation [Monoid V] (source : Coalgebra State Answer V)
    (first second : Nat) (initial : State) :
    continueRepresentation source second
      (chooseRepresentation (contributions source first initial)) =
      contributions source (first + second) initial := by
  rw [continueRepresentation, restore_chooseRepresentation, contributions_add]
  rfl

/-- Accepted replies do not inspect the coalgebra when given more budget. -/
theorem continue_single_representation [Monoid V] (source : Coalgebra State Answer V)
    (fuel : Nat) (reply : Option (Answer × V)) :
    continueRepresentation source fuel (.inl reply) =
      restoreRepresentation (State := State) (.inl reply) := by
  cases reply with
  | none => rfl
  | some item =>
      simp [continueRepresentation, restoreRepresentation, WeightedResumption.sequence]

/-- Completion is checked on the entire retained frontier. Once closed,
extra budget executes no source instructions and changes no coefficients. -/
theorem closed_cut_stable [Monoid V] (source : Coalgebra State Answer V)
    (first second : Nat) (initial : State)
    (closed : (contributions source first initial).all (fun leaf => leaf.1.isLeft) = true) :
    contributions source (first + second) initial = contributions source first initial := by
  rw [contributions_add]
  exact continue_without_pending source second _ closed

/-- An accepted retained cut remains the same reply under every continuation
budget, without re-executing already returned work. -/
theorem singleResult_resume [Monoid V] (source : Coalgebra State Answer V)
    (first second : Nat) (initial : State) (reply : Option (Answer × V))
    (accepted : singleResult? (contributions source first initial) = some reply) :
    singleResult? (contributions source (first + second) initial) = some reply := by
  rw [closed_cut_stable source first second initial
    (singleResult_closed _ reply accepted)]
  exact accepted

/-- The separately constructed free handler has exactly the same admission
and complete retained reply as the direct frontier algorithm. -/
theorem handler_singleResult [Monoid V] (source : Coalgebra State Answer V)
    (fuel : Nat) (initial : State) :
    singleResult? (interpret catalogue (cut source fuel initial)) =
      singleResult? (contributions source fuel initial) := by
  rw [interpret_cut]

theorem completed_cardinality_stable [Monoid V] (source : Coalgebra State Answer V)
    (first second : Nat) (initial : State) (grade : Grade)
    (closed : (contributions source first initial).all (fun leaf => leaf.1.isLeft) = true) :
    Allows grade (returnedContributions (contributions source (first + second) initial)).length ↔
      Allows grade (returnedContributions (contributions source first initial)).length := by
  rw [closed_cut_stable source first second initial closed]

namespace Controls

def lateDuplicate : Coalgebra Nat Nat Nat
  | 0 => .inr [(1, 1), (2, 1)]
  | 1 => .inl 7
  | 2 => .inr [(3, 1)]
  | _ => .inl 7

theorem singleton_prefix_is_not_complete :
    contributions lateDuplicate 2 0 = [(.inl 7, 1), (.inr 3, 1)] ∧
      Allows .one (returnedContributions (contributions lateDuplicate 2 0)).length ∧
      singleResult? (contributions lateDuplicate 2 0) = none := by decide

theorem late_equal_answer_is_retained :
    contributions lateDuplicate 3 0 = [(.inl 7, 1), (.inl 7, 1)] ∧
      ¬ Allows .optional (returnedContributions (contributions lateDuplicate 3 0)).length ∧
      singleResult? (contributions lateDuplicate 3 0) = none := by decide

theorem singleton_prefix_fallback_keeps_remainder :
    chooseRepresentation (contributions lateDuplicate 2 0) =
      .inr [(.inl 7, 1), (.inr 3, 1)] := by decide

theorem fallback_resumption_retains_duplicate :
    continueRepresentation lateDuplicate 1
      (chooseRepresentation (contributions lateDuplicate 2 0)) =
      [(.inl 7, 1), (.inl 7, 1)] := by decide

def failure : Coalgebra Nat Nat Nat := fun _ => .inr []

theorem closed_failure_is_not_det :
    singleResult? (contributions failure 1 0) = some none ∧
      ¬ Allows .one (returnedContributions (contributions failure 1 0)).length := by decide

def zeroWeight : Coalgebra Nat Nat Nat
  | 0 => .inr [(1, 0)]
  | _ => .inl 7

theorem zero_weight_success_is_det :
    singleResult? (contributions zeroWeight 2 0) = some (some (7, 0)) ∧
      Allows .one (returnedContributions (contributions zeroWeight 2 0)).length := by decide

theorem accepted_zero_weight_remains_unchanged (extra : Nat) :
    singleResult? (contributions zeroWeight (2 + extra) 0) = some (some (7, 0)) :=
  singleResult_resume zeroWeight 2 extra 0 (some (7, 0)) (by decide)

def silent : Coalgebra Nat Nat Nat := fun state => .inr [(state, 1)]

theorem silent_cut_remains_pending (fuel state : Nat) :
    contributions silent fuel state = [(.inr state, 1)] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [contributions, silent, WeightedResumption.sequence, ih]

theorem zero_answers_do_not_establish_failure (fuel state : Nat) :
    returnedContributions (contributions silent fuel state) = [] ∧
      singleResult? (contributions silent fuel state) = none := by
  rw [silent_cut_remains_pending]
  exact ⟨rfl, rfl⟩

/-- A calling-mode restriction can select one branch. An unbound relational
call keeps both physical occurrences, even when their values coincide. -/
def modeSource (bound : Bool) : Coalgebra Nat Nat Nat
  | 0 => .inr (if bound then [(1, 1)] else [(1, 1), (1, 1)])
  | _ => .inl 7

theorem calling_mode_changes_singleResult :
    singleResult? (contributions (modeSource true) 2 0) = some (some (7, 1)) ∧
      singleResult? (contributions (modeSource false) 2 0) = none := by decide

theorem same_weight_total_different_cardinality :
    total ([(7, 2)] : Contributions Nat Nat) = total [(7, 1), (7, 1)] ∧
      ([(7, 2)] : Contributions Nat Nat).length ≠ [(7, 1), (7, 1)].length := by decide

theorem dependent_bind_is_not_sampled_product :
    (WeightedResumption.sequence ([(false, 1), (true, 1)] : Contributions Bool Nat)
      (fun bound => if bound then [(7, 1), (8, 1)] else [(7, 1)])).length = 3 := by decide

theorem singleton_cardinality_does_not_determine_retained_effects :
    singleResult? (State := Nat) ([((.inl (7, ["left", "right"])), 1)] :
      Contributions ((Nat × List String) ⊕ Nat) Nat) ≠
    singleResult? (State := Nat) [((.inl (7, ["right", "left"])), 1)] := by decide

end Controls
end Mettapedia.GSLT.Dynamics.WeightedBranchingCardinality
