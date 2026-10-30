import Mettapedia.Algorithms.Compression.RelationalPruning

/-! Positive and negative finite controls for relational completion guards. -/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.RelationalPruningControls

open Algorithms.Compression.RelationalPruning

private def task : Examples Nat Nat := ⟨[(0, 2)], [(0, 99)], true⟩
private def vocabulary : List Nat := [0, 1, 1, 4, 2, 3]
private def relation : Nat → Nat → List Nat
  | 1, 0 => [1, 1]
  | 1, 1 => [2]
  | 4, 1 => [2]
  | 2, 0 => [2]
  | 3, 0 => [99]
  | _, _ => []

theorem chain_keeps_all_six_successful_occurrences :
    pruned vocabulary (fun _ => vocabulary) (fun left => chainGuard task.positive (relation left))
      (fun left right => consistent task (chain (relation left) (relation right))) =
        [(1, 1), (1, 1), (1, 4), (1, 1), (1, 1), (1, 4)] := by decide

theorem choice_halves_complete_checks :
    completeChecks vocabulary (fun _ => vocabulary) = 36 ∧
      guardedChecks vocabulary (fun _ => vocabulary) (fun left => choiceGuard task (relation left)) = 18 := by decide

theorem choice_keeps_all_five_successes :
    pruned vocabulary (fun _ => vocabulary) (fun left => choiceGuard task (relation left))
      (fun left right => consistent task (choice (relation left) (relation right))) =
        [(0, 2), (4, 2), (2, 0), (2, 4), (2, 2)] := by decide

theorem missing_final_value_is_not_an_empty_prefix :
    2 ∉ relation 1 0 ∧ chainGuard task.positive (relation 1) = true ∧
      consistent task (chain (relation 1) (relation 4)) = true := by decide

theorem missing_choice_answer_can_be_repaired :
    chainGuard task.positive (relation 0) = false ∧ choiceGuard task (relation 0) = true ∧
      consistent task (choice (relation 0) (relation 2)) = true := by decide

theorem negative_prefix_answer_can_disappear_in_a_chain :
    let examples : Examples Nat Nat := ⟨[(0, 2)], [(0, 1)], true⟩
    choiceGuard examples (relation 1) = false ∧
      consistent examples (chain (relation 1) (relation 4)) = true := by decide

theorem equal_duplicate_answers_are_functional :
    choice (relation 2) (relation 2) 0 = [2, 2] ∧
      consistent task (choice (relation 2) (relation 2)) = true := by decide

theorem no_suffix_repairs_an_empty_chain_prefix (suffix : Nat → List Nat) :
    ¬ Accepts task (chain (relation 0) suffix) :=
  empty_chain_prefix_rejects task (relation 0) (by decide) suffix

theorem no_suffix_removes_a_forbidden_choice_answer (suffix : Nat → List Nat) :
    ¬ Accepts task (choice (relation 3) suffix) :=
  bad_choice_prefix_rejects task (relation 3) (by decide) suffix

#print axioms consistent_iff
#print axioms chainGuard_iff
#print axioms chain_guard_necessary
#print axioms choiceGuard_iff
#print axioms choice_guard_necessary
#print axioms empty_chain_prefix_rejects
#print axioms bad_choice_prefix_rejects
#print axioms pruned_eq_reference
#print axioms chain_candidates_preserved
#print axioms choice_candidates_preserved
#print axioms fold_pruned_eq_reference
#print axioms complete_cost_selection_preserved
#print axioms complete_cost_minimum_in_preserved_region
#print axioms guarded_checks_le
#print axioms chain_keeps_all_six_successful_occurrences
#print axioms choice_halves_complete_checks
#print axioms choice_keeps_all_five_successes
#print axioms missing_final_value_is_not_an_empty_prefix
#print axioms missing_choice_answer_can_be_repaired
#print axioms negative_prefix_answer_can_disappear_in_a_chain
#print axioms equal_duplicate_answers_are_functional
#print axioms no_suffix_repairs_an_empty_chain_prefix
#print axioms no_suffix_removes_a_forbidden_choice_answer

end Mettapedia.Examples.Compression.RelationalPruningControls
