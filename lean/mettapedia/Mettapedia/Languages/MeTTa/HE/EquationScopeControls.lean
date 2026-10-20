import Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery
import Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery
import Mettapedia.Languages.MeTTa.HE.RecursiveControls
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Equation-scope positive and negative controls

Controls expose the incoming-name collision of index-named rule instances,
show the retained evaluator agreeing with Hyperon Experimental on nested and
recursive calls of one equation, exercise scoped query execution, and retain
source positions and occurrences. General scope and query laws are proved in
the imported modules.
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
  have dedup : (["x#0"] : List String).eraseDups = ["x#0"] := by decide
  have avoid : ScopedEquationQuery.avoidNames [] query incoming nativeIncoming =
      ["x#0", "x#0"] := by
    simp [ScopedEquationQuery.avoidNames, EquationScope.visibleNames,
      EquationScope.bindingNames, query, incoming, nativeIncoming, encodeModelAtom,
      encodeModelAtoms, Metta.Atom.vars, Metta.Bindings.vars, dedup]
  have legacyCollision : ("x#" ++ Nat.repr 0 : String) = "x#0" := by decide
  have fallback : Metta.Minimal.captureAvoidingName ["x#0", "x#0"] 0 "x" =
      "#######x#0" := by decide
  rw [ScopedEquationQuery.freshRule,
    LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule, avoid]
  simp [lhs, rhs, encodeModelAtom, decodeModelAtom, Metta.Minimal.freshenRuleAvoiding,
    Metta.Minimal.freshenRule, Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup,
    legacyCollision, fallback, Metta.Minimal.renameAllVars]

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
  simp only [encodeModelAtom, encodeModelAtoms, query, match_identity,
    scoped_merge, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filterMap_cons, List.filterMap_nil, scoped_bindings_loop_free,
    Bool.false_eq_true, if_false, scoped_new_value, decodeModelAtom]

/-- A call-only avoidance set is insufficient when the continuation still
holds the old generated name. The declarative coverage premise rejects it. -/
theorem call_only_scope_misses_pending_variable :
    ¬CoversEvaluation (equationScope [] query Atom.atomType Bindings.empty)
      [.var "x#0"] query Atom.atomType Bindings.empty := by
  intro covered
  have liveMember : "x#0" ∈ equationScope [.var "x#0"] query Atom.atomType Bindings.empty := by
    simp [equationScope, atomListVariables, atomVariables]
  have forbidden := covered "x#0" liveMember
  simp [equationScope, atomListVariables, atomVariables, query, Atom.atomType,
    Bindings.empty, Bindings.names] at forbidden

theorem pending_variable_keeps_its_name_unbound :
    (mettaCall space GroundedDispatch.none query Atom.atomType Bindings.empty 16
      [.var "x#0"]).map (fun result => (result.1, result.2.lookup "x#0")) =
      [(.symbol "b", none)] := by decide +kernel

theorem reference_empty_seed_returns_value :
    (mettaCall space GroundedDispatch.none query Atom.atomType Bindings.empty 16).map Prod.fst =
      [.symbol "b"] := by decide +kernel

/-- Negative control: the index-named rule instance reuses the incoming key
`x#0`, so merging its match with the incoming record conflicts and the answer is
lost. -/
theorem index_named_instance_conflicts_with_incoming :
    ((queryEquations space query 16).flatMap fun hit => mergeBindings hit.2 incoming 16) = [] := by
  decide +kernel

/-- The retained evaluator renames the rule apart from the incoming record, so the
same call keeps its answer. -/
theorem retained_evaluator_keeps_value_under_incoming_key :
    (mettaCall space GroundedDispatch.none query Atom.atomType incoming 16).map Prod.fst =
      [.symbol "b"] := by decide +kernel

theorem scoped_query_retains_value : scopedResults.map ScopedEquationQuery.Hit.value =
    [.symbol "b"] := by
  rw [scoped_results_exact]
  rfl

theorem scoped_query_preserves_old_assignment :
    scopedResults.map (fun hit => decodeModelAtom (Metta.instantiate hit.bindings (.var "x#0"))) =
      [.symbol "a"] := by
  rw [scoped_results_exact]
  have value : Metta.instantiate
      [.val "#######x#0" (.sym "b"), .val "x#0" (.sym "a")] (.var "x#0") = .sym "a" := by
    rw [Metta.instantiate, Metta.Bindings.resolveAtom]
    rfl
  simp only [List.map_cons, List.map_nil, value, decodeModelAtom]

theorem visible_query_alone_misses_incoming_key :
    queryEquationsAgainstVisible space query 16 = queryEquations space query 16 := by decide +kernel

theorem normal_freshener_retains_spelling :
    EquationFreshening.freshRule [] 0 lhs rhs =
      (.expression [.symbol "identity", .var "x#0"], .var "x#0") := by
  decide +kernel

/-- Collision freedom is the source contract; no backend's private spelling
is prescribed by this control. -/
theorem collision_freshener_avoids_spelling :
    ∀ name ∈ (encodeModelAtom (EquationFreshening.freshRule ["x#0"] 0 lhs rhs).1).vars ++
        (encodeModelAtom (EquationFreshening.freshRule ["x#0"] 0 lhs rhs).2).vars,
      name ∉ ["x#0"] :=
  EquationFreshening.freshRule_variables_avoid ["x#0"] 0 lhs rhs

theorem incoming_key_is_visible : "x#0" ∈ EquationScope.visibleNames [] query incoming := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query, incoming,
    encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]

theorem incoming_value_variable_is_visible :
    "x#0" ∈ EquationScope.visibleNames [] query
      ⟨[("different", .expression [.symbol "stored", .var "x#0"])], []⟩ := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query,
    encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]

theorem equality_left_is_visible : "x#0" ∈ EquationScope.visibleNames [] query
    ⟨[], [("x#0", "other")]⟩ := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query,
    encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]

theorem equality_right_is_visible : "x#0" ∈ EquationScope.visibleNames [] query
    ⟨[], [("other", "x#0")]⟩ := by
  simp [EquationScope.visibleNames, EquationScope.bindingNames, query,
    encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]

def retained : Configuration :=
  ⟨space, .work (.call query Atom.atomType Bindings.empty 16 []),
    [.argumentTail (.var "x#0"),
      .append (.atom (.var "pending") Atom.atomType
        ⟨[("key", .var "stored")], [("left", "right")]⟩ 16 [])],
    [(.var "answered", ⟨[("answer-key", .var "answer-value")], []⟩)]⟩

theorem continuation_choice_is_visible : "x#0" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, Bindings.empty, Atom.atomType, atomVariables,
    atomListVariables]

theorem pending_alternative_is_visible : "pending" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, Bindings.empty, Atom.atomType, atomVariables,
    atomListVariables]

theorem pending_binding_keys_and_values_are_visible :
    "key" ∈ RecursiveScope.configurationNames retained ∧
      "stored" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, Bindings.empty, Atom.atomType, atomVariables,
    atomListVariables]

theorem pending_equalities_are_visible :
    "left" ∈ RecursiveScope.configurationNames retained ∧
      "right" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, Bindings.empty, Atom.atomType, atomVariables,
    atomListVariables]

theorem emitted_value_and_binding_are_visible :
    "answered" ∈ RecursiveScope.configurationNames retained ∧
      "answer-key" ∈ RecursiveScope.configurationNames retained ∧
      "answer-value" ∈ RecursiveScope.configurationNames retained := by
  simp [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, RecursiveScope.controlAtoms,
    RecursiveScope.frameAtoms, RecursiveScope.taskAtoms, RecursiveScope.bindingAtoms,
    RecursiveScope.resultAtoms, retained, query, Bindings.empty, Atom.atomType, atomVariables,
    atomListVariables]

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
    LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule,
    EquationScope.visibleNames, EquationScope.bindingNames,
    lhs, rhs, query, Bindings.empty, Metta.Bindings.empty, encodeModelAtom, encodeModelAtoms,
    Metta.Atom.vars, Metta.Bindings.vars, Metta.Minimal.freshenRuleAvoiding,
    Metta.Minimal.freshenRule, Metta.Subst.apply, Metta.Subst.lookup, decodeModelAtom]

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
  simp [query, encodeModelAtom, encodeModelAtoms, match_identity, Metta.Bindings.empty,
    Metta.Bindings.merge, Metta.Bindings.mergeOne, added,
    loopFree, value, decodeModelAtom]

private theorem empty_constant_results (counter : Nat) :
    ScopedEquationQuery.ruleResults [] query Bindings.empty Metta.Bindings.empty counter
        lhs (.symbol "a") =
      [⟨.symbol "a", [.val ("x#" ++ Nat.repr counter) (.sym "b")]⟩] := by
  have fresh : ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
      counter lhs (.symbol "a") =
      (.expression [.symbol "identity", .var ("x#" ++ Nat.repr counter)], .symbol "a") := by
    simp [ScopedEquationQuery.freshRule, ScopedEquationQuery.avoidNames,
      LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule,
      EquationScope.visibleNames, EquationScope.bindingNames,
      lhs, query, Bindings.empty, Metta.Bindings.empty, encodeModelAtom, encodeModelAtoms,
      Metta.Atom.vars, Metta.Bindings.vars, Metta.Minimal.freshenRuleAvoiding,
      Metta.Minimal.freshenRule, Metta.Subst.apply, Metta.Subst.lookup, decodeModelAtom]
  unfold ScopedEquationQuery.ruleResults
  rw [fresh]
  have added : Metta.Bindings.addVarBinding [] ("x#" ++ Nat.repr counter) (.sym "b") =
      [[.val ("x#" ++ Nat.repr counter) (.sym "b")]] := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      (Metta.Bindings.addVarBinding_fresh (Metta.Bindings.classValues_empty _)
        (by intro other impossible; cases impossible))
  have loopFree : Metta.Bindings.hasLoop [.val ("x#" ++ Nat.repr counter) (.sym "b")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simp [query, encodeModelAtom, encodeModelAtoms, match_identity, Metta.Bindings.empty,
    Metta.Bindings.merge, Metta.Bindings.mergeOne, added, loopFree,
    Metta.instantiate, Metta.Bindings.resolveAtom, decodeModelAtom]

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
  have fresh : ScopedEquationQuery.freshRule []
      (.expression [.symbol "different", .symbol "b"])
      Bindings.empty Metta.Bindings.empty 0 lhs rhs =
      (.expression [.symbol "identity", .var "x#0"], .var "x#0") := by
    have avoid : ScopedEquationQuery.avoidNames []
        (.expression [.symbol "different", .symbol "b"])
        Bindings.empty Metta.Bindings.empty = [] := by
      simp [ScopedEquationQuery.avoidNames, EquationScope.visibleNames,
        EquationScope.bindingNames, Bindings.empty, Metta.Bindings.empty,
        encodeModelAtom, encodeModelAtoms, Metta.Atom.vars, Metta.Bindings.vars]
    rw [ScopedEquationQuery.freshRule,
      LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule, avoid]
    have zero : ("x#" ++ Nat.repr 0 : String) = "x#0" := by decide
    simp [lhs, rhs, encodeModelAtom, decodeModelAtom, Metta.Minimal.freshenRuleAvoiding,
      Metta.Minimal.freshenRule, Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, zero]
  have noMatch : Metta.matchAtoms
      (.expr [.sym "identity", .var "x#0"])
      (.expr [.sym "different", .sym "b"]) = [] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll]
  unfold ScopedEquationQuery.ruleResults
  rw [fresh]
  simp [encodeModelAtom, noMatch]

theorem malformed_retained_state_rejected :
    RecursiveScope.freshRuleData (.symbol "not-a-configuration") query incoming 0 lhs rhs = none := by decide +kernel

theorem every_initial_hit_has_independent_derivation
    (hit : ScopedEquationQuery.LocatedHit) (member : hit ∈ duplicatedResults) :
    ∃ output,
      EquationQueryCandidateRel duplicatedSpace [] query Bindings.empty hit.result.value output ∧
        ScopedEquationQuery.BindingInvariant output hit.result.bindings :=
  ScopedEquationQuery.queryResults_sound ScopedEquationQuery.bindingInvariant_empty member

/-- Every actual query hit keeps its physical equation and the exact
freshened match used to derive its independent emitted work item. -/
theorem every_initial_hit_has_physical_derivation
    (hit : ScopedEquationQuery.LocatedHit) (member : hit ∈ duplicatedResults) :
    ∃ matched output,
      EquationQueryOccurrenceRel duplicatedSpace [] query Bindings.empty
        hit.position hit.lhs hit.rhs
        (ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
          hit.position hit.lhs hit.rhs).1
        (ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
          hit.position hit.lhs hit.rhs).2 matched hit.result.value output ∧
      ScopedEquationQuery.BindingInvariant output hit.result.bindings := by
  obtain ⟨_, matched, output, _, _, _, _, occurrence, invariant⟩ :=
    ScopedEquationQuery.queryResults_occurrence_sound
      ScopedEquationQuery.bindingInvariant_empty member
  exact ⟨matched, output, by simpa only [Nat.zero_add] using occurrence, invariant⟩

/-- Equal stored equations at positions one and two produce separately
justified occurrences, despite equal raw sides and equal answer values. -/
theorem duplicate_equal_rules_have_distinct_occurrences :
    ∃ first second : ScopedEquationQuery.LocatedHit,
      first ∈ duplicatedResults ∧ second ∈ duplicatedResults ∧
      first.position = 1 ∧ second.position = 2 ∧
      first.lhs = second.lhs ∧ first.rhs = second.rhs ∧
      first.result.value = second.result.value ∧
      (∃ matched output,
        EquationQueryOccurrenceRel duplicatedSpace [] query Bindings.empty first.position
          first.lhs first.rhs
          (ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
            first.position first.lhs first.rhs).1
          (ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
            first.position first.lhs first.rhs).2 matched first.result.value output) ∧
      (∃ matched output,
        EquationQueryOccurrenceRel duplicatedSpace [] query Bindings.empty second.position
          second.lhs second.rhs
          (ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
            second.position second.lhs second.rhs).1
          (ScopedEquationQuery.freshRule [] query Bindings.empty Metta.Bindings.empty
            second.position second.lhs second.rhs).2 matched second.result.value output) := by
  let first : ScopedEquationQuery.LocatedHit :=
    ⟨1, lhs, rhs, ⟨.symbol "b", [.val ("x#" ++ Nat.repr 1) (.sym "b")]⟩⟩
  let second : ScopedEquationQuery.LocatedHit :=
    ⟨2, lhs, rhs, ⟨.symbol "b", [.val ("x#" ++ Nat.repr 2) (.sym "b")]⟩⟩
  have firstMember : first ∈ duplicatedResults := by rw [duplicated_results_exact]; simp [first]
  have secondMember : second ∈ duplicatedResults := by rw [duplicated_results_exact]; simp [second]
  obtain ⟨firstMatch, firstOutput, firstOccurrence, _⟩ :=
    every_initial_hit_has_physical_derivation first firstMember
  obtain ⟨secondMatch, secondOutput, secondOccurrence, _⟩ :=
    every_initial_hit_has_physical_derivation second secondMember
  exact ⟨first, second, firstMember, secondMember, rfl, rfl, rfl, rfl, rfl,
    ⟨firstMatch, firstOutput, firstOccurrence⟩, ⟨secondMatch, secondOutput, secondOccurrence⟩⟩

/-- The declaration before the two equal rules is a physical offset, never a
successful equation occurrence. -/
theorem non_rule_offset_refuses_occurrence
    (freshPattern freshRhs emitted : Atom) (matched output : Bindings) :
    ¬EquationQueryOccurrenceRel duplicatedSpace [] query Bindings.empty 0 lhs rhs
      freshPattern freshRhs matched emitted output := by
  intro occurrence
  have stored := occurrence.stored
  simp [duplicatedSpace, Space.ofList] at stored

/-- A successful existential candidate cannot be attached to another row
whose raw RHS differs, even when the left-hand side is identical. -/
theorem wrong_rule_position_refuses_occurrence
    (freshPattern freshRhs emitted : Atom) (matched output : Bindings) :
    ¬EquationQueryOccurrenceRel duplicatedSpace [] query Bindings.empty 3 lhs rhs
      freshPattern freshRhs matched emitted output := by
  intro occurrence
  have stored := occurrence.stored
  simp [duplicatedSpace, Space.ofList, rule, rhs] at stored

/-- The finite query enumerator contains a hit at exactly its physical row.
The legacy candidate projection cannot make either wrong position valid. -/
theorem source_enumeration_and_wrong_position
    (hit : ScopedEquationQuery.LocatedHit) (member : hit ∈ duplicatedResults) :
    duplicatedSpace.atoms[hit.position]? =
        some (.expression [.symbol "=", hit.lhs, hit.rhs]) ∧
      hit.position ≠ 0 := by
  have stored := (ScopedEquationQuery.queryResults_mem_iff _ _ _ _ _ _ _).mp member |>.1
  refine ⟨stored, ?_⟩
  intro zero
  rw [zero] at stored
  simp [duplicatedSpace, Space.ofList] at stored

/-- A source-only derivation, independent of the executable query's results. -/
def constantOccurrenceSpace : Space := Space.ofList
  [.symbol "offset", .expression [.symbol "=", .symbol "source", .symbol "answer"]]

private theorem empty_model : HEBindingSatisfied (fun name => .var name) Bindings.empty := by
  constructor
  · intro name value member
    simp [Bindings.empty] at member
  · intro left right member
    simp [Bindings.empty] at member

theorem constant_independent_occurrence :
    EquationQueryOccurrenceRel constantOccurrenceSpace [] (.symbol "source") Bindings.empty 1
      (.symbol "source") (.symbol "answer") (.symbol "source") (.symbol "answer")
      Bindings.empty (.symbol "answer") Bindings.empty := by
  refine ⟨by rfl, ⟨?_, .symSym "source" semanticLoopFree_empty⟩, ⟨?_, ?_⟩⟩
  · refine ⟨id, fun _ _ equal => equal, .symbol _, .symbol _, ?_⟩
    intro name occurs
    rcases occurs with left | right <;> cases ‹AtomOccurs _ _›
  · exact MergeRel.logicalMerge (.mk (by simp [constraints, Bindings.empty]) MergeConstraintsRel.nil)
      ⟨_, specTypeBindingSatisfied_of_heBindingSatisfied empty_model⟩
  · intro valuation satisfied
    rfl

/-- The chosen-fresh-pair completeness theorem realizes that independent
source occurrence at its original physical offset. -/
theorem independent_occurrence_is_realized :
    ∃ result : ScopedEquationQuery.Hit,
      (⟨1, .symbol "source", .symbol "answer", result⟩ : ScopedEquationQuery.LocatedHit) ∈
        ScopedEquationQuery.queryResults constantOccurrenceSpace [] (.symbol "source")
          Bindings.empty Metta.Bindings.empty 0 ∧
      LeaBindingSolutionTheoryEquiv Bindings.empty result.bindings ∧
      ∀ valuation, HEBindingSatisfied valuation Bindings.empty →
        HEAtomEquationSatisfied valuation result.value (.symbol "answer") := by
  apply ScopedEquationQuery.occurrence_observational_complete
    ScopedEquationQuery.bindingInvariant_empty
  convert constant_independent_occurrence using 1 <;>
    simp [ScopedEquationQuery.freshRule, ScopedEquationQuery.avoidNames,
      LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule,
      EquationScope.visibleNames, EquationScope.bindingNames,
      Bindings.empty, Metta.Bindings.empty, encodeModelAtom, Metta.Atom.vars, Metta.Bindings.vars,
      Metta.Minimal.freshenRuleAvoiding, Metta.Minimal.freshenRule,
      decodeModelAtom]

/-! ## Independent alpha transport with retained caller names -/

def alphaLive : List Atom := [.expression [.var "caller", .var "nested"]]
def alphaSpace : Space := Space.ofList
  [.symbol "offset", .expression [.symbol "=", .var "raw", .var "raw"]]
def alphaMatched : Bindings := Bindings.empty.assign "raw#7" (.symbol "answer")

private theorem alpha_source_variant : AlphaVariantRel alphaLive (.symbol "answer") Bindings.empty
    (.var "raw") (.var "raw") (.var "raw#7") (.var "raw#7") := by
  have visible : EquationScope.visibleNames alphaLive (.symbol "answer") Bindings.empty =
      ["caller", "nested"] := by
    simp [EquationScope.visibleNames, EquationScope.bindingNames, alphaLive,
      Bindings.empty, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]
  have fresh : EquationFreshening.freshRule
      (EquationScope.visibleNames alphaLive (.symbol "answer") Bindings.empty) 7
      (.var "raw") (.var "raw") = (.var "raw#7", .var "raw#7") := by
    rw [visible]
    decide +kernel
  simpa only [fresh] using EquationFreshening.freshRule_alphaVariant alphaLive (.symbol "answer")
    (.var "raw") (.var "raw") Bindings.empty 7

/-- The independent source uses private spelling raw#7, whereas the actual
physical row's scoped query uses its own chosen counter. The retained caller
names occur at nonzero syntax depth. -/
theorem private_source_occurrence :
    ∃ output,
      EquationQueryOccurrenceRel alphaSpace alphaLive (.symbol "answer") Bindings.empty 1
        (.var "raw") (.var "raw") (.var "raw#7") (.var "raw#7") alphaMatched
        (.var "raw#7") output := by
  have noOccurrence : ¬AtomOccurs (.symbol "answer") "raw#7" := by intro occurs; cases occurs
  have loopFree : SemanticLoopFree alphaMatched := semanticLoopFree_single_assignment noOccurrence
  have matched : MatchRel equalityGroundedSemantic (.symbol "answer") (.var "raw#7") alphaMatched :=
    .nonVarVar (by rfl) loopFree
  have model : HEBindingSatisfied (fun _ => .sym "answer") alphaMatched := by
    change (∀ name (value : Atom), (name, value) ∈ [("raw#7", Atom.symbol "answer")] → _) ∧ _
    constructor
    · intro name value member
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
      simp only [encodeModelAtom, applyClassSolution]
    · change ∀ name other, (name, other) ∈ ([] : List (String × String)) → _
      simp
  have incomingModel : HEBindingSatisfied (fun _ => .sym "answer") Bindings.empty := by
    constructor <;> simp [Bindings.empty]
  obtain ⟨output, merged, satisfied, _⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution incomingModel
      ScopedEquationQuery.bindingInvariant_empty.semantic.specAssignmentsNonVariable model
      (Spec.Match.ModelTheory.specMatch_assignmentsNonVariable matched)
  refine ⟨output, ⟨by rfl, ⟨alpha_source_variant, matched⟩,
    ⟨(merged.logicalMerge ⟨_, specTypeBindingSatisfied_of_heBindingSatisfied satisfied⟩).comm,
      ?_⟩⟩⟩
  intro valuation satisfies
  rfl

/-- That independently specified occurrence produces an actual native hit at
physical offset one, retaining a paired output and fixing both live names. -/
theorem arbitrary_private_variant_is_realized :
    ∃ permutation : Equiv.Perm String, ∃ output result,
      permutation "caller" = "caller" ∧ permutation "nested" = "nested" ∧
      (⟨1, .var "raw", .var "raw", result⟩ : ScopedEquationQuery.LocatedHit) ∈
        ScopedEquationQuery.queryResults alphaSpace alphaLive (.symbol "answer")
          Bindings.empty Metta.Bindings.empty 0 ∧
      ScopedEquationQuery.BindingInvariant output result.bindings := by
  obtain ⟨sourceOutput, source⟩ := private_source_occurrence
  obtain ⟨permutation, _, output, result, fixed, member, _, invariant, _, _⟩ :=
    ScopedEquationQuery.occurrence_arbitrary_alpha_complete
      ScopedEquationQuery.bindingInvariant_empty (counter := 0) source
  have caller : QueryVisibleName alphaLive (.symbol "answer") Bindings.empty "caller" :=
    (EquationScope.mem_visibleNames_iff _ _ _ _).mp (by
      simp [EquationScope.visibleNames, EquationScope.bindingNames, alphaLive,
        Bindings.empty, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars])
  have nestedName : QueryVisibleName alphaLive (.symbol "answer") Bindings.empty "nested" :=
    (EquationScope.mem_visibleNames_iff _ _ _ _).mp (by
      simp [EquationScope.visibleNames, EquationScope.bindingNames, alphaLive,
        Bindings.empty, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars])
  exact ⟨permutation, output, result, fixed _ caller, fixed _ nestedName, member, invariant⟩

private theorem alpha_rule_results_exact :
    ScopedEquationQuery.ruleResults alphaLive (.symbol "answer") Bindings.empty
      Metta.Bindings.empty 1 (.var "raw") (.var "raw") =
        [⟨.symbol "answer", [.val "raw#1" (.sym "answer")]⟩] := by
  have visible : EquationScope.visibleNames alphaLive (.symbol "answer") Bindings.empty =
      ["caller", "nested"] := by
    simp [EquationScope.visibleNames, EquationScope.bindingNames, alphaLive,
      Bindings.empty, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]
  have fresh : ScopedEquationQuery.freshRule alphaLive (.symbol "answer") Bindings.empty
      Metta.Bindings.empty 1 (.var "raw") (.var "raw") =
      (.var "raw#1", .var "raw#1") := by
    have avoid : ScopedEquationQuery.avoidNames alphaLive (.symbol "answer")
        Bindings.empty Metta.Bindings.empty = ["caller", "nested"] := by
      simp [ScopedEquationQuery.avoidNames, visible, Metta.Bindings.empty,
        Metta.Bindings.vars, List.eraseDups]
    have one : ("raw#" ++ Nat.repr 1 : String) = "raw#1" := by decide
    rw [ScopedEquationQuery.freshRule,
      LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule, avoid]
    simp [encodeModelAtom, decodeModelAtom, Metta.Minimal.freshenRuleAvoiding,
      Metta.Minimal.freshenRule, Metta.Atom.vars, Metta.Subst.apply,
      Metta.Subst.lookup, one]
  have added : Metta.Bindings.addVarBinding [] "raw#1" (.sym "answer") =
      [[.val "raw#1" (.sym "answer")]] := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      (Metta.Bindings.addVarBinding_fresh (Metta.Bindings.classValues_empty "raw#1")
        (by intro other impossible; cases impossible))
  have loopFree : Metta.Bindings.hasLoop [.val "raw#1" (.sym "answer")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  have value : Metta.instantiate [.val "raw#1" (.sym "answer")] (.var "raw#1") =
      .sym "answer" :=
    Metta.instantiate_singleton_val_var_of_not_mem _ _ (by simp [Metta.Atom.vars])
  unfold ScopedEquationQuery.ruleResults
  rw [fresh]
  simp [encodeModelAtom, Metta.matchAtoms, Metta.matchAtomsWith,
    Metta.Bindings.empty, Metta.Bindings.merge, Metta.Bindings.mergeOne,
    added, loopFree, value, decodeModelAtom]

/-- The source spelling differs from the native chosen spelling; the actual
query still returns the same constant without an evaluation-fuel parameter. -/
theorem private_variant_native_answer :
    (ScopedEquationQuery.queryResults alphaSpace alphaLive (.symbol "answer")
      Bindings.empty Metta.Bindings.empty 0).map (fun hit => hit.result.value) = [.symbol "answer"] := by
  simp [ScopedEquationQuery.queryResults, alphaSpace, Space.ofList, alpha_rule_results_exact]

/-- Caller freshness is necessary: a permutation fixing a public variable
cannot simultaneously turn that variable into a distinct private spelling. -/
theorem missing_freshness_prevents_public_fixed_transport :
    ¬∃ permutation : Equiv.Perm String,
      permutation "caller" = "caller" ∧
      Spec.Type.RuntimeRefinement.renameTypeVars permutation (.var "caller") = .var "private" := by
  rintro ⟨permutation, fixed, renamed⟩
  have impossible : ("caller" : String) = "private" := by
    simpa only [Spec.Type.RuntimeRefinement.renameTypeVars, Atom.var.injEq, fixed] using renamed
  exact (by decide : ("caller" : String) ≠ "private") impossible

/-- Private spellings cannot be compared by equality of unrenamed full
solution theories. Reindexing the valuation is part of the contract. -/
theorem unrenamed_private_theories_differ :
    HEBindingSatisfied
      (fun name => if name = "raw#7" then .sym "answer" else .sym "different") alphaMatched ∧
    ¬HEBindingSatisfied
      (fun name => if name = "raw#7" then .sym "answer" else .sym "different")
      (Bindings.empty.assign "raw#1" (.symbol "answer")) := by
  constructor
  · change (∀ name (value : Atom), (name, value) ∈ [("raw#7", Atom.symbol "answer")] → _) ∧ _
    constructor
    · intro name value member
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
      simp [encodeModelAtom, applyClassSolution]
    · change ∀ name other, (name, other) ∈ ([] : List (String × String)) → _
      simp
  · intro satisfied
    have wrong := satisfied.1 "raw#1" (.symbol "answer") (by decide +kernel)
    have impossible : (Metta.Atom.sym "different") = .sym "answer" := by
      simpa only [encodeModelAtom, applyClassSolution,
        if_neg (by decide : ("raw#1" : String) ≠ "raw#7")] using wrong
    exact (by decide : ("different" : String) ≠ "answer") (Metta.Atom.sym.inj impossible)

/-! ## Actual query work items retain their caller and changed bindings -/

def actualAlphaPrevious : Metta.Minimal.Stack :=
  [{ atom := .expr [.sym "saved", .expr [.var "caller", .var "nested"]],
     vars := ["frameOnly"] }]

/-- The independent occurrence is stated over the actual interpreter's
retained stack scope, rather than an empty or query-only environment. -/
theorem actual_stack_private_source_occurrence :
    ∃ output,
      EquationQueryOccurrenceRel alphaSpace (LeaTTaScopedQuery.liveScope actualAlphaPrevious)
        (.symbol "answer") (QueryBindingProjection.project []) 1
        (.var "raw") (.var "raw") (.var "raw#7") (.var "raw#7")
        alphaMatched (.var "raw#7") output := by
  obtain ⟨output, source⟩ := private_source_occurrence
  have visible : EquationScope.visibleNames (LeaTTaScopedQuery.liveScope actualAlphaPrevious)
      (.symbol "answer") Bindings.empty = ["frameOnly", "caller", "nested"] := by
    simp [EquationScope.visibleNames, EquationScope.bindingNames,
      LeaTTaScopedQuery.liveScope, actualAlphaPrevious, Metta.Minimal.liveStackVars,
      Bindings.empty, encodeModelAtom, Metta.Atom.vars]
  have fresh : EquationFreshening.freshRule
      (EquationScope.visibleNames (LeaTTaScopedQuery.liveScope actualAlphaPrevious)
        (.symbol "answer") Bindings.empty) 7
      (.var "raw") (.var "raw") = (.var "raw#7", .var "raw#7") := by
    rw [visible]
    decide +kernel
  have variant := EquationFreshening.freshRule_alphaVariant
    (LeaTTaScopedQuery.liveScope actualAlphaPrevious) (.symbol "answer")
    (.var "raw") (.var "raw") Bindings.empty 7
  rw [fresh] at variant
  exact ⟨output, ⟨source.stored, ⟨variant, source.selected.2⟩, source.result⟩⟩

/-- A source occurrence at physical row one is realized at runtime counter
five. Both explicit frame scope and nested caller syntax are protected. -/
theorem actual_query_realizes_private_source_with_saved_caller :
    ∃ permutation : Equiv.Perm String, ∃ emitted merged item,
      permutation "caller" = "caller" ∧ permutation "nested" = "nested" ∧
      permutation "frameOnly" = "frameOnly" ∧
      item ∈ Metta.Minimal.queryOpItemsOfRule actualAlphaPrevious (.sym "answer") [] 5
        (.var "raw", .var "raw") ∧
      item = Metta.Minimal.evalResult actualAlphaPrevious (encodeModelAtom emitted) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged := by
  obtain ⟨output, source⟩ := actual_stack_private_source_occurrence
  obtain ⟨permutation, emitted, _, _, _, merged, item, fixed, _, _, _, member, itemEq,
    _, paired, _, _⟩ :=
    LeaTTaScopedQuery.queryOpItemsOfRule_occurrence_arbitrary_alpha_complete
      (counter := 5) LeaTTaBridge.leaBindingsHEImage_empty
      LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty source
  have visible (name : String) (member : name ∈ ["frameOnly", "caller", "nested"]) :
      QueryVisibleName (LeaTTaScopedQuery.liveScope actualAlphaPrevious)
        (.symbol "answer") (QueryBindingProjection.project []) name := by
    apply (EquationScope.mem_visibleNames_iff _ _ _ _).mp
    simpa [EquationScope.visibleNames, EquationScope.bindingNames,
      LeaTTaScopedQuery.liveScope, actualAlphaPrevious, Metta.Minimal.liveStackVars,
      QueryBindingProjection.project, leaEqualityEdges, encodeModelAtom, Metta.Atom.vars] using member
  exact ⟨permutation, emitted, merged, item,
    fixed _ (visible _ (by simp)), fixed _ (visible _ (by simp)),
    fixed _ (visible _ (by simp)), member, itemEq, paired⟩

/-- The exact actual query item keeps the full saved caller and the new
private assignment. It is already merged when delivered to `evalResult`. -/
theorem actual_query_item_keeps_saved_caller_and_binding :
    Metta.Minimal.queryOpItemsOfRule actualAlphaPrevious (.sym "answer") [] 5
      (.var "raw", .var "raw") =
      [Metta.Minimal.finItem actualAlphaPrevious (.sym "answer")
        [.val "raw#5" (.sym "answer")]] := by
  have five : Nat.repr 5 = "5" := by decide
  have loopFree : Metta.Bindings.hasLoop [.val "raw#5" (.sym "answer")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simp [Metta.Minimal.queryOpItemsOfRule, Metta.Minimal.queryOpAvoid,
    actualAlphaPrevious, Metta.Minimal.liveStackVars, Metta.Atom.vars, Metta.Bindings.vars,
    Metta.Minimal.freshenRuleAvoiding, Metta.Minimal.freshenRule,
    Metta.Subst.apply, Metta.Subst.lookup, five, Metta.matchAtoms, Metta.matchAtomsWith,
    Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, loopFree,
    Metta.instantiate, Metta.Bindings.resolveAtom]
  rfl

/-- The independent private source occurrence also earns a normal finite
source entry for the exact computed query item. The caller and fresh changed
binding frame in that item are retained while choosing its source presentation. -/
theorem actual_private_query_has_normal_source_entry :
    ∃ permutation : Equiv.Perm String,
    ∃ presentation : Spec.Type.Presentation.TypeSubst, ∃ value merged,
      presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation (QueryBindingProjection.project merged)) ∧
      Metta.Minimal.finItem actualAlphaPrevious (.sym "answer")
          [.val "raw#5" (.sym "answer")] =
        Metta.Minimal.evalResult actualAlphaPrevious (encodeModelAtom value) merged ∧
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel
        (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation (.var "raw#7"))) value ∧
      Spec.Type.Presentation.BindingTheory.EquationListPresentationRel
        (Spec.Type.Presentation.BindingTheory.bindingAtomEquations (QueryBindingProjection.project merged))
        [] presentation ∧
      Spec.Type.Presentation.BindingTheory.BindingMaterializationRel (QueryBindingProjection.project merged)
        (Spec.Type.RuntimeRefinement.renameTypeVars permutation (.var "raw#7"))
        (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation (.var "raw#7"))) := by
  obtain ⟨output, source⟩ := actual_stack_private_source_occurrence
  obtain ⟨permutation, presentation, value, merged, item, _, member, entry, _,
    normal, theory, _, alpha, _, _, _, _, _, fold, materialized⟩ :=
    LeaTTaScopedQuery.queryOpItemsOfRule_occurrence_normal_presentation_complete
      (counter := 5) leaBindingsHEImage_empty
      LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty source
  change item ∈ Metta.Minimal.queryOpItemsOfRule actualAlphaPrevious (.sym "answer") [] 5
    (.var "raw", .var "raw") at member
  rw [actual_query_item_keeps_saved_caller_and_binding] at member
  have itemExact := List.mem_singleton.mp member
  exact ⟨permutation, presentation, value, merged, normal, theory, itemExact ▸ entry, alpha, fold, materialized⟩

/-- A value-only observer misses the loss of the surrounding computation. -/
theorem dropping_saved_caller_changes_actual_item :
    (Metta.Minimal.evalResult actualAlphaPrevious (.sym "answer")
      [.val "raw#5" (.sym "answer")]).stack ≠
    (Metta.Minimal.evalResult [] (.sym "answer")
      [.val "raw#5" (.sym "answer")]).stack := by
  intro same
  have tails := congrArg List.tail same
  change actualAlphaPrevious = [] at tails
  simp [actualAlphaPrevious] at tails

/-- Returning the old empty bindings would erase the newly solved private
variable even though the emitted constant remains unchanged. -/
theorem dropping_changed_bindings_changes_actual_item :
    (Metta.Minimal.evalResult actualAlphaPrevious (.sym "answer")
      [.val "raw#5" (.sym "answer")]).bnd ≠
    (Metta.Minimal.evalResult actualAlphaPrevious (.sym "answer") []).bnd := by
  simp [Metta.Minimal.evalResult, Metta.Minimal.finItem]

/-! ## Nested and recursive calls of one equation

Each program below is a Hyperon Experimental conformance fixture; the stated
values are the ones the reference interpreter prints. Results are multisets, so
nondeterministic families are compared up to permutation with multiplicity.
The negative control shows the failure these laws repair: an inner call leaves
its rule-local binding in the record, and an index-named instance of the same
equation for the outer call collides with it. -/

namespace NestedCalls

def app (items : List Atom) : Atom := .expression items
def equation (lhs rhs : Atom) : Atom := app [sym "=", lhs, rhs]
def succ (atom : Atom) : Atom := app [sym "S", atom]
def zero : Atom := sym "Z"

/-- Retained evaluator values of one top-level query, with multiplicity. -/
def values (space : Space) (atom : Atom) : List Atom := (eval space atom).map Prod.fst

def incSpace : Space := Space.ofList [equation (app [sym "inc", .var "x"]) (succ (.var "x"))]

def addSpace : Space := Space.ofList
  [equation (app [sym "add", zero, .var "y"]) (.var "y"),
    equation (app [sym "add", succ (.var "x"), .var "y"])
      (succ (app [sym "add", .var "x", .var "y"]))]

def paritySpace : Space := Space.ofList
  [equation (app [sym "even", zero]) (sym "True"),
    equation (app [sym "even", succ (.var "n")]) (app [sym "odd", .var "n"]),
    equation (app [sym "odd", zero]) (sym "False"),
    equation (app [sym "odd", succ (.var "n")]) (app [sym "even", .var "n"])]

def twinSpace : Space := Space.ofList
  [equation (app [sym "coin"]) (sym "H"),
    equation (app [sym "coin"]) (sym "T"),
    equation (app [sym "twin", .var "x"]) (app [.var "x", .var "x"])]

def sideSpace : Space := Space.ofList
  [equation (app [sym "side", .var "x"]) (app [sym "L", .var "x"]),
    equation (app [sym "side", .var "x"]) (app [sym "R", .var "x"])]

def probeSpace : Space := Space.ofList
  [equation (app [sym "mk"]) (succ (.var "y")),
    equation (app [sym "probe", .var "p"])
      (app [sym "unify", .var "p", app [sym "pair", succ (sym "A"), succ (sym "B")],
        sym "ok", sym "no"])]

/-- Fixture `he_nested_equation_call`: `!(inc (inc Z))` gives `[(S (S Z))]`. -/
theorem inc_twice : values incSpace (app [sym "inc", app [sym "inc", zero]]) =
    [succ (succ zero)] := by decide +kernel

/-- Fixture `he_nested_equation_call_triple`. -/
theorem inc_three_times :
    values incSpace (app [sym "inc", app [sym "inc", app [sym "inc", zero]]]) =
      [succ (succ (succ zero))] := by decide +kernel

/-- Fixture `he_recursive_peano_add`: two plus three. -/
theorem add_two_three :
    values addSpace (app [sym "add", succ (succ zero), succ (succ (succ zero))]) =
      [succ (succ (succ (succ (succ zero))))] := by decide +kernel

/-- Fixture `he_nested_recursive_add`: a recursive call in argument position. -/
theorem add_nested_argument :
    values addSpace (app [sym "add", succ (succ zero), app [sym "add", succ zero, zero]]) =
      [succ (succ (succ zero))] := by decide +kernel

/-- Fixture `he_mutual_recursion_even`. -/
theorem three_is_not_even : values paritySpace (app [sym "even", succ (succ (succ zero))]) =
    [sym "False"] := by decide +kernel

/-- Fixture `he_mutual_recursion_odd`. -/
theorem three_is_odd : values paritySpace (app [sym "odd", succ (succ (succ zero))]) =
    [sym "True"] := by decide +kernel

/-- Fixture `he_nested_nondet_twin`: each branch of the inner choice is copied
whole, so exactly two answers remain. -/
theorem twin_of_twin_coin :
    (values twinSpace (app [sym "twin", app [sym "twin", app [sym "coin"]]])).Perm
      [app [app [sym "H", sym "H"], app [sym "H", sym "H"]],
        app [app [sym "T", sym "T"], app [sym "T", sym "T"]]] := by decide +kernel

/-- Fixture `he_nested_nondet_argument`: two equations nested twice give all four
combinations, each once. -/
theorem side_of_side :
    (values sideSpace (app [sym "side", app [sym "side", zero]])).Perm
      [app [sym "L", app [sym "R", zero]], app [sym "R", app [sym "R", zero]],
        app [sym "L", app [sym "L", zero]], app [sym "R", app [sym "L", zero]]] := by
  decide +kernel

/-- Negative control for `side_of_side`: the multiset has four distinct members,
so a result list that lost or duplicated a combination would differ. -/
theorem side_of_side_not_three :
    ¬ (values sideSpace (app [sym "side", app [sym "side", zero]])).Perm
      [app [sym "L", app [sym "R", zero]], app [sym "R", app [sym "R", zero]],
        app [sym "L", app [sym "L", zero]]] := by decide +kernel

/-- Fixture `he_existential_rhs_instances_distinct`: the two calls of `mk` get
separate copies of its right-hand-side variable, so each unifies with its own
argument. -/
theorem separate_instances_unify_separately :
    values probeSpace (app [sym "probe", app [sym "pair", app [sym "mk"], app [sym "mk"]]]) =
      [sym "ok"] := by decide +kernel

/-- Fixture `he_shared_variable_unify_refused`: the same variable used twice
cannot take both values. -/
theorem shared_variable_refuses_two_values :
    values probeSpace (app [sym "probe", app [sym "pair", succ (.var "v"), succ (.var "v")]]) =
      [sym "no"] := by decide +kernel

/-- The record the inner call `(inc Z)` leaves behind. -/
def innerRecord : Bindings := ⟨[("x#0", zero)], []⟩

theorem inner_call_record :
    evalAtom incSpace GroundedDispatch.none (app [sym "inc", zero]) Atom.undefinedType
      Bindings.empty 100 = [(succ zero, innerRecord)] := by decide +kernel

/-- Negative control: the index-named instance `(inc $x#0)` of the outer call
reuses the inner call's key, its match `x#0 = (S Z)` conflicts with `x#0 = Z`,
and the nested call loses its value. -/
theorem index_named_outer_instance_loses_value :
    ((queryEquations incSpace (app [sym "inc", succ zero]) 100).flatMap fun hit =>
      mergeBindings hit.2 innerRecord 100) = [] := by decide +kernel

/-- The scoped instance of the outer call is named `x#1`, apart from the inner
key, so both assignments survive the merge. -/
theorem scoped_outer_instance_keeps_value :
    ((queryEquationsAvoiding
        (equationScope [] (app [sym "inc", succ zero]) Atom.undefinedType innerRecord)
        incSpace (app [sym "inc", succ zero]) 100).flatMap fun hit =>
      (mergeBindings hit.2 innerRecord 100).map fun merged => (hit.1, merged)) =
      [(succ (.var "x#1"), ⟨[("x#1", succ zero), ("x#0", zero)], []⟩)] := by
  decide +kernel

end NestedCalls

end Mettapedia.Languages.MeTTa.HE.EquationScopeControls


namespace Mettapedia.Languages.MeTTa.HE.EquationScopeControls.BindingLayout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.Merge

def left : Bindings :=
  ⟨[("x", .expression [.symbol "f", .var "y"]), ("y", .symbol "Z")],
    [("x", "z"), ("u", "v")]⟩

def right : Bindings :=
  ⟨[("y", .symbol "Z"), ("x", .expression [.symbol "f", .var "y"])],
    [("u", "v"), ("x", "z")]⟩

theorem reordered_record_keeps_cycle_decision : left.hasLoop = right.hasLoop := by
  apply hasLoop_eq_of_relation_membership_iff <;>
    intro relation <;> simp [left, right, or_comm]

def beforeAlias : Bindings :=
  Bindings.empty.assign "x" (.expression [.symbol "f", .var "y"])

def afterAlias : Bindings := beforeAlias.addEquality "x" "y"

theorem open_assignment_is_admitted : SemanticLoopFree beforeAlias := by
  apply semanticLoopFree_single_assignment
  rw [← mem_vars_iff_atomOccurs]
  decide

theorem adding_an_alias_can_create_a_cycle : afterAlias.hasLoop = true := by
  rw [hasLoop_eq_true_iff_cycle]
  refine ⟨"x", .single ?_⟩
  refine ⟨"x", .expression [.symbol "f", .var "y"], "y", ?_, ?_, ?_, ?_, ?_⟩
  · simp [afterAlias, beforeAlias, Bindings.addEquality,
      Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup]
  · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
  · exact .expression (by simp) (.var "y")
  · apply EqualityClosure.mem_eqClass_iff_reachable.mpr
    exact SimpleGraph.Adj.reachable (by
      simp [EqualityClosure.edgeGraph_adj_iff, afterAlias, beforeAlias,
        Bindings.addEquality, Bindings.assign, Bindings.empty])
  · simp

end Mettapedia.Languages.MeTTa.HE.EquationScopeControls.BindingLayout
