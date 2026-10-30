import Mettapedia.Languages.Datalog.ClosureCompletion
import Mettapedia.Languages.Datalog.ComparisonControls

/-! Executable separating controls for source fact closure and logical keys.
The corresponding ordinary-source/native execution join is separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Datalog.Closure.Controls

private def policy := Comparisons.Controls.integerPolicy

private def atom (name : String) : Atom := ⟨[name], []⟩
private def fact (name : String) : GroundFact := ⟨[name], []⟩
private def rule (head body : String) : Statement :=
  .rule ⟨atom head, [.atom (atom body)]⟩

private def cyclic : Program := ⟨[
  rule "B" "A", rule "C" "A", rule "D" "B", rule "D" "C", rule "A" "D"]⟩

private def after (ticks : Nat) : State := run policy cyclic ticks (initial [fact "A"])

private def key (statementIndex : Nat) (premise : String) : DerivationKey :=
  ⟨statementIndex, [], [fact premise]⟩

theorem prefix_is_pending :
    completion policy cyclic (after 0) = .pending ∧
      completion policy cyclic (after 1) = .pending := by
  decide +kernel

theorem facts_settle_before_the_key_account :
    (after 2).facts.toFinset = {fact "A", fact "B", fact "C", fact "D"} ∧
      (after 2).keys.length = 4 ∧
      completion policy cyclic (after 2) = .factsOnly ∧
      completion policy cyclic (after 3) = .factsAndKeys ∧
      (after 3).keys.length = 5 := by
  decide +kernel

theorem two_explanations_one_fact_survive_the_cycle :
    key 2 "B" ∈ (after 3).keys ∧ key 3 "C" ∈ (after 3).keys ∧
      key 2 "B" ≠ key 3 "C" ∧
      (after 3).facts.count (fact "D") = 1 ∧
      (after 3).keys.count (key 4 "D") = 1 := by
  decide +kernel

theorem duplicate_validation_and_replay_do_not_create_keys :
    run policy cyclic 3 (initial [fact "A", fact "A"]) = after 3 ∧
      after 6 = after 3 := by
  decide +kernel

theorem interrupted_execution_resumes_exactly :
    run policy cyclic 2 (after 1) = after 3 := by
  exact (run_add policy cyclic 1 2 (initial [fact "A"])).symm

theorem a_missing_seed_is_a_settled_empty_region :
    (run policy cyclic 3 (initial [])).facts = [] ∧
      (run policy cyclic 3 (initial [])).keys = [] ∧
      completion policy cyclic (initial []) = .factsAndKeys := by
  decide +kernel

theorem wrong_conclusions_and_wrong_keys_are_absent :
    fact "Wrong" ∉ (after 3).facts ∧ key 99 "A" ∉ (after 3).keys ∧
      key 2 "C" ∉ (after 3).keys := by
  decide +kernel

private def refused : Program := ⟨[
  .rule ⟨atom "Bad", [.atom (atom "A"),
    .comparison ⟨.less, .literal (.number 1), .literal (.number 0)⟩]⟩]⟩

theorem failed_guards_publish_neither_fact_nor_key :
    let result := run policy refused 2 (initial [fact "A"])
    result.facts = [fact "A"] ∧ result.keys = [] ∧
      completion policy refused result = .factsAndKeys := by
  decide +kernel

theorem general_bound_applies_to_the_actual_cycle :
    (factUniverse cyclic [fact "A"]).card = 4 ∧
      completion policy cyclic
        (run policy cyclic ((factUniverse cyclic [fact "A"]).card + 1) (initial [fact "A"])) =
        .factsAndKeys :=
  ⟨by decide +kernel, fullClosure_by_bound policy cyclic [fact "A"]⟩

theorem known_head_still_records_a_new_source_rule :
    let duplicated : Program := ⟨[rule "B" "A", rule "B" "A"]⟩
    let result := run policy duplicated 1 (initial [fact "A", fact "B"])
    result.facts.count (fact "B") = 1 ∧
      result.keys = [key 0 "A", key 1 "A"] ∧
      completion policy duplicated result = .factsAndKeys := by
  decide +kernel

#print axioms facts_settle_before_the_key_account
#print axioms two_explanations_one_fact_survive_the_cycle
#print axioms interrupted_execution_resumes_exactly
#print axioms failed_guards_publish_neither_fact_nor_key
#print axioms general_bound_applies_to_the_actual_cycle

end Mettapedia.Languages.Datalog.Closure.Controls
