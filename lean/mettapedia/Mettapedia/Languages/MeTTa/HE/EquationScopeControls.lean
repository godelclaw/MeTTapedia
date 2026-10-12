import Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery
import Mettapedia.Languages.MeTTa.HE.RecursiveControls

/-!
# Equation-scope positive and negative controls

Controls expose the incoming-name collision in the older reference evaluator,
exercise scoped query execution, and retain source positions and occurrences.
General scope and query laws are proved in the imported modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationScopeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance RecursiveTasks RecursiveEncoding
open Spec.Match.Merge Spec.Eval.Steps

def lhs : Atom := .expression [.symbol "identity", .var "x"]
def rhs : Atom := .var "x"
def query : Atom := .expression [.symbol "identity", .symbol "b"]
def rule : Atom := .expression [.symbol "=", lhs, rhs]
def space : Space := Space.ofList [rule]
def incoming : Bindings := ⟨[("x#0", .symbol "a")], []⟩
def nativeIncoming : Metta.Bindings := [.val "x#0" (.sym "a")]

def scopedResults : List ScopedEquationQuery.Hit :=
  ScopedEquationQuery.ruleResults [] query incoming nativeIncoming 0 lhs rhs

private theorem match_identity (name : String) :
    Metta.matchAtoms (.expr [.sym "identity", .var name])
      (.expr [.sym "identity", .sym "b"]) =
      [[.val name (.sym "b")]] := by
  have added : Metta.Bindings.addVarBinding [] name (.sym "b") =
      [[.val name (.sym "b")]] := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      (Metta.Bindings.addVarBinding_fresh (Metta.Bindings.classValues_empty name)
        (by intro other impossible; cases impossible))
  have loopFree : Metta.Bindings.hasLoop [.val name (.sym "b")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  have matched : Metta.matchAtomsWith none
      (.expr [.sym "identity", .var name]) (.expr [.sym "identity", .sym "b"]) =
      [[.val name (.sym "b")]] := by
    simp only [Metta.matchAtomsWith]
    unfold Metta.matchAll
    simp [Metta.matchAtomsWith, Metta.Bindings.merge]
    unfold Metta.matchAll
    simp [Metta.matchAtomsWith, Metta.Bindings.merge]
    unfold Metta.matchAll
    simp [loopFree, Metta.Bindings.mergeOne, added]
  rw [Metta.matchAtoms, matched]
  simp [loopFree]

private theorem scoped_fresh_rule :
    ScopedEquationQuery.freshRule [] query incoming nativeIncoming 0 lhs rhs =
      (.expression [.symbol "identity", .var "#######x#0"], .var "#######x#0") := by
  have zero : Nat.repr 0 = "0" := by decide
  simp [ScopedEquationQuery.freshRule, ScopedEquationQuery.avoidNames,
    EquationFreshening.freshRule, EquationScope.visibleNames, EquationScope.bindingNames,
    lhs, rhs, query, incoming, nativeIncoming, toLeaTTaAtom, toLeaTTaAtoms,
    Metta.Atom.vars, Metta.Bindings.vars, Metta.Minimal.freshenRuleAvoiding,
    Metta.Minimal.freshenRule, Metta.Subst.apply, Metta.Subst.lookup, zero,
    Metta.Minimal.renameAllVars, Metta.Minimal.captureAvoidingName,
    Metta.Minimal.avoidancePrefix, fromLeaTTaAtom, fromLeaTTaAtoms]
  decide +kernel

private theorem scoped_merge :
    Metta.Bindings.merge nativeIncoming [.val "#######x#0" (.sym "b")] =
      [[.val "#######x#0" (.sym "b"), .val "x#0" (.sym "a")]] := by
  have different : ("#######x#0" : String) ≠ "x#0" := by decide
  simp [nativeIncoming, Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, different,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal]

private theorem scoped_bindings_loop_free :
    Metta.Bindings.hasLoop
      [.val "#######x#0" (.sym "b"), .val "x#0" (.sym "a")] = false := by
  simp only [Metta.Bindings.hasLoop, Metta.Bindings.vars, List.flatMap_cons,
    List.flatMap_nil, Metta.Atom.vars, List.append_nil, List.cons_append, List.nil_append]
  rfl

private theorem scoped_new_value :
    Metta.instantiate [.val "#######x#0" (.sym "b"), .val "x#0" (.sym "a")]
      (.var "#######x#0") = .sym "b" := by
  rw [Metta.instantiate, Metta.Bindings.resolveAtom]
  rfl

private theorem scoped_results_exact : scopedResults =
    [⟨.symbol "b", [.val "#######x#0" (.sym "b"), .val "x#0" (.sym "a")]⟩] := by
  unfold scopedResults ScopedEquationQuery.ruleResults
  rw [scoped_fresh_rule]
  simp only [toLeaTTaAtom, toLeaTTaAtoms, query, match_identity,
    scoped_merge, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filterMap_cons, List.filterMap_nil, scoped_bindings_loop_free,
    Bool.false_eq_true, if_false, scoped_new_value, fromLeaTTaAtom]

theorem reference_empty_seed_returns_value :
    (mettaCall space GroundedDispatch.none query Atom.atomType Bindings.empty 16).map Prod.fst =
      [.symbol "b"] := by decide +kernel

theorem reference_incoming_collision_loses_value :
    (mettaCall space GroundedDispatch.none query Atom.atomType incoming 16).map Prod.fst = [] := by decide +kernel

theorem scoped_query_retains_value : scopedResults.map ScopedEquationQuery.Hit.value =
    [.symbol "b"] := by
  rw [scoped_results_exact]
  rfl

theorem scoped_query_preserves_old_assignment :
    scopedResults.map (fun hit => fromLeaTTaAtom (Metta.instantiate hit.bindings (.var "x#0"))) =
      [.symbol "a"] := by
  rw [scoped_results_exact]
  have value : Metta.instantiate
      [.val "#######x#0" (.sym "b"), .val "x#0" (.sym "a")] (.var "x#0") = .sym "a" := by
    rw [Metta.instantiate, Metta.Bindings.resolveAtom]
    rfl
  simp only [List.map_cons, List.map_nil, value, fromLeaTTaAtom]

theorem visible_query_alone_misses_incoming_key :
    queryEquationsAgainstVisible space query 16 = queryEquations space query 16 := by decide +kernel

theorem normal_freshener_retains_spelling :
    EquationFreshening.freshRule [] 0 lhs rhs =
      (.expression [.symbol "identity", .var "x#0"], .var "x#0") := by
  have zero : Nat.repr 0 = "0" := by decide
  simp [EquationFreshening.freshRule, Metta.Minimal.freshenRuleAvoiding,
    Metta.Minimal.freshenRule, lhs, rhs, toLeaTTaAtom, fromLeaTTaAtom,
    Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, zero]

theorem collision_freshener_avoids_spelling :
    EquationFreshening.freshRule ["x#0"] 0 lhs rhs =
      (.expression [.symbol "identity", .var "####x#0"], .var "####x#0") := by
  have zero : Nat.repr 0 = "0" := by decide
  simp [EquationFreshening.freshRule, Metta.Minimal.freshenRuleAvoiding,
    Metta.Minimal.freshenRule, lhs, rhs, toLeaTTaAtom, fromLeaTTaAtom,
    Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, zero,
    Metta.Minimal.renameAllVars, Metta.Minimal.captureAvoidingName,
    Metta.Minimal.avoidancePrefix]
  decide +kernel

theorem incoming_key_is_visible : "x#0" ∈ EquationScope.visibleNames [] query incoming := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query, incoming,
    toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem incoming_value_variable_is_visible :
    "x#0" ∈ EquationScope.visibleNames [] query
      ⟨[("different", .expression [.symbol "stored", .var "x#0"])], []⟩ := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query,
    toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem equality_left_is_visible : "x#0" ∈ EquationScope.visibleNames [] query
    ⟨[], [("x#0", "other")]⟩ := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query,
    toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem equality_right_is_visible : "x#0" ∈ EquationScope.visibleNames [] query
    ⟨[], [("other", "x#0")]⟩ := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query,
    toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

def retained : Configuration :=
  ⟨space, .work (.call query Atom.atomType Bindings.empty 16),
    [.argumentTail (.var "x#0"),
      .append (.atom (.var "pending") Atom.atomType
        ⟨[("key", .var "stored")], [("left", "right")]⟩ 16)],
    [(.var "answered", ⟨[("answer-key", .var "answer-value")], []⟩)]⟩

theorem continuation_choice_is_visible : "x#0" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem pending_alternative_is_visible : "pending" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem pending_binding_keys_and_values_are_visible :
    "key" ∈ RecursiveScope.configurationNames retained ∧
      "stored" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem pending_equalities_are_visible :
    "left" ∈ RecursiveScope.configurationNames retained ∧
      "right" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

theorem emitted_value_and_binding_are_visible :
    "answered" ∈ RecursiveScope.configurationNames retained ∧
      "answer-key" ∈ RecursiveScope.configurationNames retained ∧
      "answer-value" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

def nested : Nat → Atom → Atom
  | 0, atom => atom
  | depth + 1, atom => .expression [nested depth atom]

theorem nested_variable_occurs (depth : Nat) (name : String) :
    AtomOccurs (nested depth (.var name)) name := by
  induction depth with
  | zero => exact .var name
  | succ depth ih => exact .expression (by simp) ih

theorem arbitrary_depth_is_visible (depth : Nat) (name : String) :
    name ∈ EquationScope.visibleNames [nested depth (.var name)] query incoming :=
  EquationScope.retained_occurrence_mem (by simp) (nested_variable_occurs depth name)

theorem bounded_scan_can_miss_nested_names : collectVars (nested 8 (.var "x#0")) 2 = [] := by decide +kernel

private theorem empty_fresh_rule (counter : Nat) :
    ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty counter lhs rhs =
      (.expression [.symbol "identity", .var ("x#" ++ Nat.repr counter)],
        .var ("x#" ++ Nat.repr counter)) := by
  simp [ScopedEquationQuery.freshRule, ScopedEquationQuery.avoidNames,
    EquationFreshening.freshRule, EquationScope.visibleNames, EquationScope.bindingNames,
    lhs, rhs, query, Bindings.empty, Metta.Bindings.empty, toLeaTTaAtom, toLeaTTaAtoms,
    Metta.Atom.vars, Metta.Bindings.vars, Metta.Minimal.freshenRuleAvoiding,
    Metta.Minimal.freshenRule, Metta.Subst.apply, Metta.Subst.lookup, fromLeaTTaAtom]

private theorem empty_identity_results (counter : Nat) :
    ScopedEquationQuery.ruleResults [] query Bindings.empty Metta.Bindings.empty counter lhs rhs =
      [⟨.symbol "b", [.val ("x#" ++ Nat.repr counter) (.sym "b")]⟩] := by
  unfold ScopedEquationQuery.ruleResults
  rw [empty_fresh_rule]
  have added : Metta.Bindings.addVarBinding [] ("x#" ++ Nat.repr counter) (.sym "b") =
      [[.val ("x#" ++ Nat.repr counter) (.sym "b")]] := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      (Metta.Bindings.addVarBinding_fresh (Metta.Bindings.classValues_empty _)
        (by intro other impossible; cases impossible))
  have loopFree : Metta.Bindings.hasLoop [.val ("x#" ++ Nat.repr counter) (.sym "b")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  have value : Metta.instantiate [.val ("x#" ++ Nat.repr counter) (.sym "b")]
      (.var ("x#" ++ Nat.repr counter)) = .sym "b" :=
    Metta.instantiate_singleton_val_var_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simp [query, toLeaTTaAtom, toLeaTTaAtoms, match_identity, Metta.Bindings.empty,
    Metta.Bindings.merge, Metta.Bindings.mergeOne, added,
    loopFree, value, fromLeaTTaAtom]

private theorem empty_constant_results (counter : Nat) :
    ScopedEquationQuery.ruleResults [] query Bindings.empty Metta.Bindings.empty counter
        lhs (.symbol "a") =
      [⟨.symbol "a", [.val ("x#" ++ Nat.repr counter) (.sym "b")]⟩] := by
  have fresh : ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
      counter lhs (.symbol "a") =
      (.expression [.symbol "identity", .var ("x#" ++ Nat.repr counter)], .symbol "a") := by
    simp [ScopedEquationQuery.freshRule, ScopedEquationQuery.avoidNames,
      EquationFreshening.freshRule, EquationScope.visibleNames, EquationScope.bindingNames,
      lhs, query, Bindings.empty, Metta.Bindings.empty, toLeaTTaAtom, toLeaTTaAtoms,
      Metta.Atom.vars, Metta.Bindings.vars, Metta.Minimal.freshenRuleAvoiding,
      Metta.Minimal.freshenRule, Metta.Subst.apply, Metta.Subst.lookup, fromLeaTTaAtom]
  unfold ScopedEquationQuery.ruleResults
  rw [fresh]
  have added : Metta.Bindings.addVarBinding [] ("x#" ++ Nat.repr counter) (.sym "b") =
      [[.val ("x#" ++ Nat.repr counter) (.sym "b")]] := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      (Metta.Bindings.addVarBinding_fresh (Metta.Bindings.classValues_empty _)
        (by intro other impossible; cases impossible))
  have loopFree : Metta.Bindings.hasLoop [.val ("x#" ++ Nat.repr counter) (.sym "b")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simp [query, toLeaTTaAtom, toLeaTTaAtoms, match_identity, Metta.Bindings.empty,
    Metta.Bindings.merge, Metta.Bindings.mergeOne, added, loopFree,
    Metta.instantiate, Metta.Bindings.resolveAtom, fromLeaTTaAtom]

def duplicatedSpace : Space := Space.ofList
  [.expression [.symbol ":", .symbol "unused", .symbol "T"], rule, rule,
    .expression [.symbol "=", lhs, .symbol "a"]]

def duplicatedResults : List ScopedEquationQuery.LocatedHit :=
  ScopedEquationQuery.queryResults duplicatedSpace [] query Bindings.empty Metta.Bindings.empty 0

private theorem duplicated_results_exact : duplicatedResults =
    [⟨1, lhs, rhs, ⟨.symbol "b", [.val ("x#" ++ Nat.repr 1) (.sym "b")]⟩⟩,
     ⟨2, lhs, rhs, ⟨.symbol "b", [.val ("x#" ++ Nat.repr 2) (.sym "b")]⟩⟩,
     ⟨3, lhs, .symbol "a", ⟨.symbol "a", [.val ("x#" ++ Nat.repr 3) (.sym "b")]⟩⟩] := by
  simp [duplicatedResults, ScopedEquationQuery.queryResults, duplicatedSpace,
    Space.ofList, rule, empty_identity_results, empty_constant_results]

theorem source_positions_retained : duplicatedResults.map ScopedEquationQuery.LocatedHit.position =
    [1, 2, 3] := by rw [duplicated_results_exact]; rfl

theorem ordered_duplicate_values_retained :
    duplicatedResults.map (fun hit => hit.result.value) = [.symbol "b", .symbol "b", .symbol "a"] := by
  rw [duplicated_results_exact]
  rfl

theorem mismatched_head_rejected :
    (ScopedEquationQuery.ruleResults [] (.expression [.symbol "different", .symbol "b"])
      Bindings.empty Metta.Bindings.empty 0 lhs rhs).map ScopedEquationQuery.Hit.value = [] := by
  have zero : Nat.repr 0 = "0" := by decide
  conv_lhs =>
    simp [ScopedEquationQuery.ruleResults, ScopedEquationQuery.freshRule,
      ScopedEquationQuery.avoidNames, EquationFreshening.freshRule,
      EquationScope.visibleNames, EquationScope.bindingNames, lhs, rhs,
      Bindings.empty, Metta.Bindings.empty, toLeaTTaAtom, toLeaTTaAtoms,
      Metta.Atom.vars, Metta.Bindings.vars, Metta.Minimal.freshenRuleAvoiding,
      Metta.Minimal.freshenRule, Metta.Subst.apply, Metta.Subst.lookup, zero,
      fromLeaTTaAtom]
  simp only [Metta.matchAtoms, Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp
  unfold Metta.matchAll
  simp

theorem malformed_retained_state_rejected :
    RecursiveScope.freshRuleData (.symbol "not-a-configuration") query incoming 0 lhs rhs = none := by decide +kernel

theorem every_initial_hit_has_independent_derivation
    (hit : ScopedEquationQuery.LocatedHit) (member : hit ∈ duplicatedResults) :
    ∃ output,
      EquationQueryCandidateRel duplicatedSpace [] query Bindings.empty hit.result.value output ∧
        ScopedEquationQuery.BindingInvariant output hit.result.bindings :=
  ScopedEquationQuery.queryResults_sound ScopedEquationQuery.bindingInvariant_empty member

end Mettapedia.Languages.MeTTa.HE.EquationScopeControls
