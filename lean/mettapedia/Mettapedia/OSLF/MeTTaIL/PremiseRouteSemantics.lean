import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Compatible premise executions as relational routes

The step interpretation uses the existing premise engine, including its
binding merges and external relation environment. Route support is exactly
membership in that engine's result list. It observes possible final bindings;
it does not identify list order or the multiplicity of identical answers.

The generic context theorem justifies deleting a repeated freshness check
inside any premise sequence. Conflicting relation queries illustrate why
separate success is insufficient for compatible composition.
-/

namespace Mettapedia.OSLF.MeTTaIL.PremiseRouteSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics

abbrev Event (_ _ : Unit) := Premise

def interpretation (environment : RelationEnv) (language : LanguageDef) : Semantics Event where
  State _ := Bindings
  step premise initial final :=
    PLift (final ∈ premiseStepWithEnv environment language initial premise)

def route : List Premise → Route Event () ()
  | [] => .refl ()
  | premise :: remaining => .cons premise (route remaining)

theorem route_append (first second : List Premise) :
    route (first ++ second) = (route first).append (route second) := by
  induction first with
  | nil => rfl
  | cons premise remaining ih => simp only [List.cons_append, route, Route.append, ih]

variable (environment : RelationEnv) (language : LanguageDef)

theorem supports_single_iff (premise : Premise) (initial final : Bindings) :
    (interpretation environment language).Supports (route [premise]) initial final ↔
      final ∈ premiseStepWithEnv environment language initial premise := by
  constructor
  · rintro ⟨⟨middle, accepted, equal⟩⟩
    cases equal.down.down
    exact accepted.down
  · intro accepted
    exact ⟨⟨final, ⟨accepted⟩, ⟨⟨rfl⟩⟩⟩⟩

/-- Exact agreement with the existing executable engine, with no alternate
matching or binding semantics. -/
theorem supports_engine_iff (premises : List Premise) (initial final : Bindings) :
    (interpretation environment language).Supports (route premises) initial final ↔
      final ∈ applyPremisesWithEnv environment language premises initial := by
  induction premises using List.reverseRecOn generalizing final with
  | nil =>
      change Nonempty (ULift (PLift (initial = final))) ↔ final ∈ [initial]
      simp only [List.mem_singleton]
      constructor
      · rintro ⟨⟨⟨equal⟩⟩⟩
        exact equal.symm
      · intro equal
        exact ⟨⟨⟨equal.symm⟩⟩⟩
  | append_singleton before premise ih =>
      rw [route_append]
      refine ((interpretation environment language).supports_append_iff
        (route before) (route [premise]) initial final).trans ?_
      simp only [applyPremisesWithEnv, List.foldl_append, List.foldl_cons,
        List.foldl_nil, List.mem_flatMap]
      exact exists_congr fun middle => and_congr (ih middle)
        (supports_single_iff environment language premise middle final)

/-- A relation on a middle block is consumed by the actual engine in any
fixed prefix and suffix, retaining the exact final binding list. -/
theorem replacement_preserves_engine (initialBlock finalBlock : List Premise)
    {original replacement : List Premise}
    (transport : (interpretation environment language).Replacement
      (route original) (route replacement))
    {initial final : Bindings}
    (accepted : final ∈ applyPremisesWithEnv environment language
      ((initialBlock ++ original) ++ finalBlock) initial) :
    final ∈ applyPremisesWithEnv environment language
      ((initialBlock ++ replacement) ++ finalBlock) initial := by
  have supported := (supports_engine_iff environment language
    ((initialBlock ++ original) ++ finalBlock) initial final).mpr accepted
  rw [route_append, route_append] at supported
  have changed := (interpretation environment language).supports_of_replacement
    ((interpretation environment language).replaceInContext
      (route initialBlock) transport (route finalBlock)) supported
  apply (supports_engine_iff environment language
    ((initialBlock ++ replacement) ++ finalBlock) initial final).mp
  simpa only [route_append] using changed

/-- Freshness checks inspect bindings and leave successful bindings unchanged.
This concrete witness map removes a repeated check. -/
def dropDuplicateFreshness (condition : FreshnessCondition) :
    (interpretation environment language).Replacement
      (route [.freshness condition, .freshness condition])
      (route [.freshness condition]) where
  map := fun witness => by
    rcases witness with ⟨middle, first, next, second, equal⟩
    exact ⟨middle, first,
      ⟨⟨(premiseStepWithEnv_freshness_mem second.down).symm.trans equal.down.down⟩⟩⟩

/-- The reverse map replays the same successful inspection. -/
def duplicateFreshness (condition : FreshnessCondition) :
    (interpretation environment language).Replacement
      (route [.freshness condition])
      (route [.freshness condition, .freshness condition]) where
  map := fun witness => by
    rcases witness with ⟨middle, accepted, equal⟩
    have unchanged := premiseStepWithEnv_freshness_mem accepted.down
    refine ⟨middle, accepted, middle, ⟨?_⟩, equal⟩
    simpa only [unchanged] using accepted.down

/-- Deduplicating adjacent freshness checks preserves the engine's possible
answers in every surrounding premise sequence. -/
theorem deduplicate_freshness_iff (initialBlock finalBlock : List Premise)
    (condition : FreshnessCondition) (initial final : Bindings) :
    final ∈ applyPremisesWithEnv environment language
      ((initialBlock ++ [.freshness condition, .freshness condition]) ++ finalBlock) initial ↔
    final ∈ applyPremisesWithEnv environment language
      ((initialBlock ++ [.freshness condition]) ++ finalBlock) initial :=
  ⟨replacement_preserves_engine environment language initialBlock finalBlock
      (dropDuplicateFreshness environment language condition),
    replacement_preserves_engine environment language initialBlock finalBlock
      (duplicateFreshness environment language condition)⟩

namespace SharedBinding

def rows : RelationEnv where
  tuples name _ := if name = "first" then [[.apply "A" []]]
    else if name = "second" then [[.apply "B" []]] else []

def first : Premise := .relationQuery "first" [.fvar "x"]
def second : Premise := .relationQuery "second" [.fvar "x"]

theorem first_succeeds :
    applyPremisesWithEnv rows language [first] [] = [[("x", .apply "A" [])]] := by
  simp [applyPremisesWithEnv, first, premiseStepWithEnv, relationQueryStep, rows,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument, mergeBindings,
    Bindings.lookup, applyBindings]

theorem second_succeeds :
    applyPremisesWithEnv rows language [second] [] = [[("x", .apply "B" [])]] := by
  simp [applyPremisesWithEnv, second, premiseStepWithEnv, relationQueryStep, rows,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument, mergeBindings,
    Bindings.lookup, applyBindings]

theorem compatible_sequence :
    applyPremisesWithEnv rows language [first, first] [] =
      [[("x", .apply "A" [])]] := by
  simp [applyPremisesWithEnv, first, premiseStepWithEnv, relationQueryStep, rows,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument, mergeBindings,
    Bindings.lookup, applyBindings]

theorem conflicting_sequence :
    applyPremisesWithEnv rows language [first, second] [] = [] := by
  simp [applyPremisesWithEnv, first, second, premiseStepWithEnv, relationQueryStep, rows,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument, mergeBindings,
    Bindings.lookup, applyBindings]

/-- Both queries succeed separately, but their incompatible bindings admit
no composite route witness. -/
theorem conflicting_route (final : Bindings) :
    ¬ (interpretation rows language).Supports (route [first, second]) [] final := by
  rw [supports_engine_iff, conflicting_sequence]
  exact List.not_mem_nil

end SharedBinding
end Mettapedia.OSLF.MeTTaIL.PremiseRouteSemantics
