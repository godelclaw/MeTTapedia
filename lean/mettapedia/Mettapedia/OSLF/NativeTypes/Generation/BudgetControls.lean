import Mettapedia.OSLF.NativeTypes.Generation.ReadoutSound
import Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary

open Mettapedia.OSLF.Framework

/-!
# Actual generated queries and inference-budget exhaustion

The finite source has nonempty equations and real base reductions. One
generator checks both modal questions and the chosen conjunctive fragment.
An unfinished empty frontier is unknown; resumption uncovers an actual
reduction. The complete execution interface is available for every sorted
object in the admitted source family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BudgetControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples
open Mettapedia.OSLF.NativeTypes.Generation

def fragment : LanguageFragment := {operational := permissions}
def chosen := selectedSnapshot snapshot fragment

theorem chosen_snapshot : chosen = snapshot := by
  change ({snapshot with language := selectedLanguage language ⟨none, permissions⟩} : GeneralExecutionAdmission.Snapshot) = _
  rw [unrestricted_signature]
  rfl

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language := (fun _ => .star, fun _ => .star)
def generated := generate snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex
def weak := generate snapshot fragment Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary.conjunctiveOnly vertex

theorem equation_profile_is_accepted : generated.equationAdmission = some true := by decide +kernel
theorem weak_equation_profile_is_accepted : weak.equationAdmission = some true := equation_profile_is_accepted

theorem actual_plan : generated.plan = runtimePlan := by
  change GeneralExecutionAdmission.compile chosen permissions = runtimePlan
  rw [chosen_snapshot]
  exact Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.actual_plan

theorem actual_request (source : Pattern) :
    generated.request [] carrier source = request source := by
  change (⟨generated.plan, [], carrier, source⟩ : GeneralOccurrenceFrontier.Request) = request source
  rw [actual_plan]
  rfl

theorem literal_start : GeneralOccurrenceFrontier.start (request other) =
    {agenda := [.visit ⟨other, [], by
      rw [show (request other).root = other from
        Pattern.eraseBinderMetadata_eq_self_of_canonical (by decide +kernel)]
      exact .nil other⟩, .universe]} := by
  have canonical : other.eraseBinderMetadata = other :=
    Pattern.eraseBinderMetadata_eq_self_of_canonical (by decide +kernel)
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root,
    request, runtimePlan, canonical, List.map_nil]
  change (if Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
    language snapshot.free [] carrier other then _ else _) = _
  rw [show Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
    language snapshot.free [] carrier other = true from by decide +kernel]
  rfl

def anyTarget (source : Pattern) : InvariantTest (generated.request [] carrier source) :=
  {accepts := fun _ => true, invariant := fun _ _ _ => rfl}

def possibilityResult (source : Pattern) (budget : Nat) : CheckResult :=
  (generated.checkModal [] carrier source .possibility (anyTarget source) budget).result

theorem query_is_the_actual_frontier (source : Pattern) (budget : Nat) :
    possibilityResult source budget =
      modalReadout .possibility (generated.request [] carrier source)
        (generated.execute [] carrier source budget) (fun _ => true) := by
  simp only [possibilityResult, Generated.checkModal, equation_profile_is_accepted]
  rfl

theorem no_budget_is_unknown : possibilityResult other 0 = .unknown := by
  rw [query_is_the_actual_frontier]
  unfold Generated.execute
  rw [actual_request, literal_start]
  apply unfinished_empty_is_unknown
  · rfl
  · rfl

theorem first_funded_target :
    GeneralOccurrenceFrontier.targets (request other)
      (GeneralOccurrenceFrontier.run (request other) 16
        (GeneralOccurrenceFrontier.start (request other))) = [alpha] := by
  rw [literal_start]
  decide +kernel

/-- Resumption preserves the actual emitted receipt, even if later search
continues through equation representatives. -/
theorem funded_target_persists (more : Nat) :
    alpha ∈ GeneralOccurrenceFrontier.targets (request other)
      (GeneralOccurrenceFrontier.run (request other) (16 + more)
        (GeneralOccurrenceFrontier.start (request other))) := by
  have first : alpha ∈ GeneralOccurrenceFrontier.targets (request other)
      (GeneralOccurrenceFrontier.run (request other) 16
        (GeneralOccurrenceFrontier.start (request other))) := by
    rw [first_funded_target]
    exact List.mem_cons_self
  obtain ⟨answer, present, target⟩ := List.mem_map.mp first
  obtain ⟨tail, extended⟩ := GeneralOccurrenceFrontier.answers_prefix (request other) more
    (GeneralOccurrenceFrontier.run (request other) 16 (GeneralOccurrenceFrontier.start (request other)))
  apply List.mem_map.mpr
  refine ⟨answer, ?_, target⟩
  rw [GeneralOccurrenceFrontier.run_add, extended]
  exact List.mem_append_left tail present

theorem funded_search_discovers_reduction : possibilityResult other 40 = .decided true := by
  rw [query_is_the_actual_frontier]
  unfold Generated.execute
  rw [actual_request]
  have found : (GeneralOccurrenceFrontier.targets (request other)
      (GeneralOccurrenceFrontier.run (request other) 40
        (GeneralOccurrenceFrontier.start (request other)))).any (fun _ => true) = true :=
    List.any_eq_true.mpr ⟨alpha, funded_target_persists 24, rfl⟩
  simp only [modalReadout, found, if_true]

theorem resumed_query_preserves_actual_state :
    generated.execute [] carrier other 40 =
      GeneralOccurrenceFrontier.run _ 40 (generated.execute [] carrier other 0) :=
  generated_resume generated [] carrier other 0 40

/-- Exhaustion has not become a semantic denial: the unresolved source really
has an independently proved reduction. -/
theorem unknown_does_not_certify_absence :
    possibilityResult other 0 = .unknown ∧
      (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step other alpha :=
  ⟨no_budget_is_unknown, other_steps_alpha⟩

theorem source_fragment_and_logic_are_independent :
    weak.plan = generated.plan ∧
      weak.modalCatalogue = [] ∧ generated.modalCatalogue ≠ [] := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [weak, generate, Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary.conjunctiveOnly]
  · have nonempty : generated.modalCatalogue.length > 0 := by
      change (schemas generated.plan).length > 0
      rw [actual_plan]
      decide +kernel
    intro empty
    simp only [empty, List.length_nil, Nat.lt_irrefl] at nonempty

/-- The equation-aware completed entry point belongs to the same generator,
for every ambient context and every admitted sorted object. -/
theorem every_sorted_object_has_complete_generated_execution {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.HasType language snapshot.free bound source expected)
    (object : Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern source = true) :
    ∃ result, generated.executeCertified? bound expected source = some result ∧
      GeneralOccurrenceFrontier.complete _ result = true ∧
      GeneralOccurrenceFrontier.checkCertificate _ result = true := by
  change ∃ result, GeneralOccurrenceFrontier.executeCertified? chosen permissions bound expected source =
    some result ∧
      GeneralOccurrenceFrontier.complete
        (GeneralOccurrenceFrontier.Request.fromSnapshot chosen permissions bound expected source)
        result = true ∧
      GeneralOccurrenceFrontier.checkCertificate
        (GeneralOccurrenceFrontier.Request.fromSnapshot chosen permissions bound expected source)
        result = true
  rw [chosen_snapshot]
  exact every_typed_object_has_complete_execution typed object

end Mettapedia.OSLF.NativeTypes.Generation.BudgetControls
