import Mettapedia.OSLF.NativeTypes.Generation.EquationAdmission
import Mettapedia.OSLF.NativeTypes.Generation.StructuralCodes
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableControls
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer

open Mettapedia.OSLF.Framework

/-!
# Independent operational, logical and sort-coordinate controls

The inputs are varied one at a time. Authored equation checks reject a genuine
vertex of the computed cube; logical refusal is separate from a false answer;
constructor selection changes the term grammar. Structural codes consume the
computed sort coordinate rather than just recording it in catalogue metadata.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Structural
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)
open Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls (theory carrier)

def snapshot : Snapshot := ⟨theory, [], ⟨[], [], []⟩⟩
def fragment : LanguageFragment := {operational := {sites := .rootOnly}}
def chosen := selectedSnapshot snapshot fragment

theorem chosen_snapshot : chosen = snapshot := by
  change ({snapshot with language := selectedLanguage theory ⟨none, fragment.operational⟩} : Snapshot) = _
  rw [unrestricted_signature]
  rfl

def acceptedVertex : CubeVertex chosen.language := (fun _ => .star, fun _ => .star)
def rejectedVertex : CubeVertex chosen.language :=
  (fun _ => .star, fun slot =>
    if slot.1.val = Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Key.constructor "G" 1 && slot.2.val = 1 then .box else .star)

def accepted := generate snapshot fragment heytingFragment acceptedVertex
def rejected := generate snapshot fragment heytingFragment rejectedVertex

theorem accepted_equation_profile : accepted.equationAdmission = some true := by
  decide +kernel

theorem rejected_equation_profile : rejected.equationAdmission = some false := by
  decide +kernel

theorem actual_center_is_proper :
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center theory).Nonempty ∧
      Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center theory ≠ Finset.univ := by
  have inside : (fun _ => .star, fun _ => .star) ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center theory := by
    simp only [Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.stable_equal_profiles_admitted
  have outside :
      (fun _ => .star, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.separatedOutput theory) ∉
        Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center theory := by
    simp only [Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.stable_original_equation_couples_output_slots]
    decide
  refine ⟨⟨_, inside⟩, ?_⟩
  intro full
  apply outside
  rw [full]
  exact Finset.mem_univ _

theorem rejected_vertex_removes_the_actual_formers : rejected.structuralCatalogue = [] :=
  (inadmissible_vertex_has_no_formers snapshot fragment heytingFragment rejectedVertex
    rejected_equation_profile).2

def conjunctive := generate snapshot fragment finiteLimitFragment acceptedVertex

theorem connective_refusal_is_not_false :
    conjunctive.elaborate carrier (.neg .bottom) = .error (.unsupportedConnective .negation) ∧
    accepted.elaborate carrier .bottom =
      .ok ⟨carrier, .bottom, structuralFormers accepted.snapshot.language⟩ := by
  decide +kernel

/-- Only the logic input changes; the actual operational plan remains fixed. -/
theorem changing_connectives_preserves_execution_input : conjunctive.plan = accepted.plan := rfl

def firstConstructor : Fin accepted.snapshot.language.terms.length := ⟨0, by decide +kernel⟩

theorem actual_structural_sort_is_read : structuralOutputSort accepted firstConstructor = .star := by
  decide +kernel

/-- With equations disabled, changing a structural result coordinate forms a
different actual universe-indexed code while retaining the same language. -/
def directedSnapshot : Snapshot := ⟨Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.directedTheory, [], ⟨[], [], []⟩⟩
def directedChosen := selectedSnapshot directedSnapshot fragment
def lowVertex : CubeVertex directedChosen.language := (fun _ => .star, fun _ => .star)
def highVertex : CubeVertex directedChosen.language :=
  (fun _ => .star, fun slot => if slot.2.val = (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature directedChosen.language).arity slot.1
    then .box else .star)
def low := generate directedSnapshot fragment heytingFragment lowVertex
def high := generate directedSnapshot fragment heytingFragment highVertex
def lowConstructor : Fin low.snapshot.language.terms.length := ⟨0, by decide +kernel⟩
def highConstructor : Fin high.snapshot.language.terms.length := ⟨0, by decide +kernel⟩

theorem cube_coordinate_changes_code_result :
    structuralOutputSort low lowConstructor = .star ∧
      structuralOutputSort high highConstructor = .box ∧ low.plan = high.plan := by
  exact ⟨by decide +kernel, by decide +kernel, rfl⟩

def lowInputs : StructuralInputs low [] lowConstructor := fun position =>
  {meaning := fun term => Mettapedia.GSLT.LanguageDef.WellSorted.HasType low.snapshot.language
      low.snapshot.free [] term (structuralDeclaration low lowConstructor).params[position].typeExpr,
    bounded := fun _ inhabited => inhabited}

def highInputs : StructuralInputs high [] highConstructor := fun position =>
  {meaning := fun term => Mettapedia.GSLT.LanguageDef.WellSorted.HasType high.snapshot.language
      high.snapshot.free [] term (structuralDeclaration high highConstructor).params[position].typeExpr,
    bounded := fun _ inhabited => inhabited}

theorem low_structural_code_is_actually_formed :
    low.structuralFormer? [] lowConstructor lowInputs =
      some ⟨structuralOutputSort low lowConstructor, structuralCode low [] lowConstructor lowInputs⟩ := by
  unfold Generated.structuralFormer?
  rw [if_pos]
  decide +kernel

theorem high_structural_code_is_actually_formed :
    high.structuralFormer? [] highConstructor highInputs =
      some ⟨structuralOutputSort high highConstructor, structuralCode high [] highConstructor highInputs⟩ := by
  unfold Generated.structuralFormer?
  rw [if_pos]
  decide +kernel

/-- The dial changes the indices of produced codes, not only the recorded
coordinate or the number of generated catalogue entries. -/
theorem cube_changes_actual_produced_code_sorts :
    (low.structuralFormer? [] lowConstructor lowInputs).map Sigma.fst = some .star ∧
      (high.structuralFormer? [] highConstructor highInputs).map Sigma.fst = some .box := by
  rw [low_structural_code_is_actually_formed, high_structural_code_is_actually_formed]
  simp only [Option.map_some]
  exact ⟨congrArg some cube_coordinate_changes_code_result.1,
    congrArg some cube_coordinate_changes_code_result.2.1⟩

def onlyF : LanguageFragment := {fragment with constructorIndices := some [0]}

theorem language_selection_changes_the_actual_signature :
    (selectedLanguage theory onlyF).terms.map GrammarRule.label = ["F"] ∧
      theory.terms.map GrammarRule.label = ["F", "G"] := by
  decide +kernel

theorem language_rule_selection_changes_the_actual_executor :
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.disabled.execute [] Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.term
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.source 40).answers.length = 0 ∧
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.execution.answers.length = 1 :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.selecting_no_rules_changes_execution

end Mettapedia.OSLF.NativeTypes.Generation.Controls
