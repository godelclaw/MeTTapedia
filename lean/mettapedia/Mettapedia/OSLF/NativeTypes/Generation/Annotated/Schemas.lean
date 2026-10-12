import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Sources
import Mettapedia.OSLF.NativeTypes.Generation.ModalCodes
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceFreeExtension

open Mettapedia.OSLF.Framework

/-!
# Actual modal schemas from checked annotated source templates

The source annotation instantiates a finite authored template at its supplied
carrier. The second stage finds the original declaration in the generator's
actual compiled operational plan. Missing operational admission remains a
separate diagnostic. A successful result constructs the same modal schema,
profile and dependent type former as the finite concrete catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.Formation
open ModalHypercube (HSort)

abbrev RuleEntry (generated : Generated) :=
  {entry : RulePlan × Nat // entry ∈ generated.plan.rules.zipIdx}

def AnnotatedSource.entryMatches {generated : Generated}
    (source : AnnotatedSource generated) (entry : RuleEntry generated) : Bool :=
  decide (entry.val.1.declarationIndex = source.site.declaration ∧ entry.val.1.authored = source.site.rule)

def AnnotatedSource.ruleEntry? {generated : Generated} (source : AnnotatedSource generated) :
    Option (RuleEntry generated) :=
  generated.plan.rules.zipIdx.attach.find? source.entryMatches

structure AnnotatedSchema (generated : Generated) where
  source : AnnotatedSource generated
  entry : RuleEntry generated
  matched : source.entryMatches entry = true

def AnnotatedSchema.schema {generated : Generated} (checked : AnnotatedSchema generated) :
    Schema generated.plan where
  ordinal := checked.entry.val.2
  declaration := checked.entry.val.1
  declared := checked.entry.property
  position := checked.source.site.position
  bound := checked.source.annotation.bound
  programCarrier := checked.source.annotation.programCarrier
  focusBound := checked.source.annotation.focusBound
  focusCarrier := checked.source.annotation.focusCarrier

/-- The rule origin is found by actual declaration lookup. It is not an
annotation field supplied by the caller. -/
def AnnotatedSource.engineSchema? {generated : Generated} (source : AnnotatedSource generated) :
    Option (AnnotatedSchema generated) :=
  match found : source.ruleEntry? with
  | none => none
  | some entry => some ⟨source, entry, List.find?_some found⟩

/-- One public generator route checks both the complete annotation and the
actual operational declaration. -/
def Generated.instantiateAnnotatedSchema? (generated : Generated) (index : Nat)
    (annotation : SourceAnnotation) : Except AnnotationIssue (AnnotatedSchema generated) :=
  match generated.instantiateAnnotatedSource? index annotation with
  | .error issue => .error issue
  | .ok source =>
    match source.engineSchema? with
    | none => .error (.unresolvedOperationalDeclaration source.site.declaration)
    | some checked => .ok checked

/-- Successful instantiation retains the actual user-supplied finite
certificate, including its intermediate domains and declaration choices. -/
theorem instantiated_schema_input_retained {generated : Generated} {index : Nat}
    {annotation : SourceAnnotation} {checked : AnnotatedSchema generated}
    (produced : generated.instantiateAnnotatedSchema? index annotation = .ok checked) :
    checked.source.index = index ∧ checked.source.annotation = annotation := by
  unfold Generated.instantiateAnnotatedSchema? at produced
  cases sourceAt : generated.instantiateAnnotatedSource? index annotation with
  | error issue => simp [sourceAt] at produced
  | ok source =>
      simp only [sourceAt] at produced
      cases schemaAt : source.engineSchema? with
      | none => simp [schemaAt] at produced
      | some result =>
          simp only [schemaAt] at produced
          cases produced
          have retained := instantiated_source_input_retained sourceAt
          unfold AnnotatedSource.engineSchema? at schemaAt
          split at schemaAt
          · cases schemaAt
          · cases schemaAt
            exact retained

namespace AnnotatedSchema

variable {generated : Generated} (checked : AnnotatedSchema generated)

theorem original_authored : checked.schema.declaration.authored = checked.source.site.rule :=
  (of_decide_eq_true checked.matched).2

/-- Compilation adds its independently checked binding metadata while
retaining the complete authored declaration as a separate payload. -/
theorem compiled_rule : checked.schema.declaration.rule =
    {checked.source.site.rule with
      typeContext := checked.source.site.rule.typeContext ++
        checked.schema.declaration.binding.implicitTypes
      bindings := some checked.schema.declaration.binding.spec} := by
  unfold RulePlan.rule Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.BindingPlan.elaborate
  rw [checked.original_authored]

/-- Inferred types are appended after the authored context. Every original
lookup therefore retains its exact type, even if an extra entry shares its
name. -/
theorem authored_free_retained {name : String} {type : TypeExpr}
    (lookup : Occurrences.ruleFree checked.source.site.rule name = some type) :
    Occurrences.ruleFree checked.schema.declaration.rule name = some type := by
  rw [checked.compiled_rule]
  unfold Occurrences.ruleFree at lookup ⊢
  rw [List.find?_append]
  cases found : checked.source.site.rule.typeContext.find? (fun entry => entry.1 == name) with
  | none => simp [found] at lookup
  | some entry => simpa [found] using lookup

theorem original_declaration : checked.schema.declaration.declarationIndex = checked.source.site.declaration :=
  (of_decide_eq_true checked.matched).1

theorem typedAt :
    TypedAt generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree checked.schema.declaration.rule)
      checked.source.site.focus checked.source.site.context checked.schema.bound checked.schema.programCarrier
      checked.schema.focusBound checked.schema.focusCarrier := by
  exact checked.source.typedAt.extendFree fun lookup => checked.authored_free_retained lookup

theorem source_typed :
    HasType generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree checked.schema.declaration.rule)
      checked.schema.bound checked.schema.declaration.rule.left checked.schema.programCarrier := by
  have left : checked.schema.declaration.rule.left = checked.source.site.rule.left := by
    rw [checked.compiled_rule]
  rw [left]
  exact checked.source.source_typed.recontextualizeFree
    fun _ lookup => checked.authored_free_retained lookup

theorem focus_typed :
    HasType generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree checked.schema.declaration.rule)
      checked.schema.focusBound checked.source.site.focus checked.schema.focusCarrier :=
  checked.typedAt.focus_typed

theorem matched_variables_retained :
    checked.schema.matchedNames = RedexPosition.fvarNames checked.source.site.focus := by
  unfold Schema.matchedNames
  change ((RedexPosition.subtermAt checked.schema.declaration.authored.left checked.schema.position).map
    RedexPosition.fvarNames).getD [] = _
  rw [checked.original_authored]
  change ((RedexPosition.subtermAt checked.source.site.rule.left checked.source.site.position).map
    RedexPosition.fvarNames).getD [] = _
  unfold Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site.position
  rw [Mettapedia.OSLF.NativeTypes.Generation.Occurrences.selected_subtermAt checked.source.selected]
  rfl

theorem rely_variables_retained (name : String) :
    name ∈ checked.schema.relyNames ↔ name ∈ checked.source.site.relyNames := by
  unfold Schema.relyNames
  change name ∈ RedexPosition.relyVars checked.schema.declaration.authored.left checked.schema.position ↔ _
  rw [checked.original_authored]
  rw [Mettapedia.OSLF.NativeTypes.Generation.Occurrences.rely_names_spec]
  exact Mettapedia.OSLF.NativeTypes.Generation.Occurrences.selected_rely_member checked.source.selected name

end AnnotatedSchema

/-- Every checked source with an actually compiled declaration obtains a
schema. The lookup itself supplies the ordinal and full original rule. -/
theorem annotated_source_engine_complete {generated : Generated} (source : AnnotatedSource generated)
    (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ generated.plan.rules.zipIdx)
    (origin : declaration.declarationIndex = source.site.declaration)
    (rule : declaration.authored = source.site.rule) :
    ∃ checked, source.engineSchema? = some checked ∧ checked.source = source := by
  have entryAccepted : source.entryMatches ⟨(declaration, ordinal), declared⟩ = true := by
    simp [AnnotatedSource.entryMatches, origin, rule]
  have foundSome : source.ruleEntry?.isSome = true := by
    apply List.find?_isSome.mpr
    exact ⟨⟨(declaration, ordinal), declared⟩, List.mem_attach _ _, entryAccepted⟩
  cases found : source.ruleEntry? with
  | none => simp [found] at foundSome
  | some entry =>
    let checked : AnnotatedSchema generated := ⟨source, entry, List.find?_some found⟩
    refine ⟨checked, ?_, rfl⟩
    unfold AnnotatedSource.engineSchema?
    split
    · rename_i missing
      rw [found] at missing
      contradiction
    · rename_i actual actualAt
      have same : actual = entry := Option.some.inj (actualAt.symm.trans found)
      subst actual
      rfl

/-- Annotated formation uses the generator's actual three dials and profile.
It extends the finite concrete catalogue only after computationally checked
source typing and operational lookup have both succeeded. -/
def Generated.annotatedModalFormer? (generated : Generated) (checked : AnnotatedSchema generated)
    (inputs : ModalInputs checked.schema (generated.modalParameters? checked.schema)) :
    Option (Σ sort : HSort,
      TypeCode generated.plan checked.schema.focusBound checked.schema.focusCarrier sort) :=
  if generated.equationAdmission = some true ∧ generated.logicFragment.core.modal = true then
    match computed : generated.modalParameters? checked.schema with
    | none => none
    | some parameters =>
      let supplied : ModalInputs checked.schema (some parameters) := computed ▸ inputs
      some ⟨parameters.output, generatedFormer checked.schema parameters.inputs
        parameters.output parameters.output supplied.1 supplied.2⟩
  else none

/-- The code is produced before any inhabitant or evidence is assumed. -/
theorem annotated_modal_formation_complete {generated : Generated} (checked : AnnotatedSchema generated)
    (inputs : ModalInputs checked.schema (generated.modalParameters? checked.schema))
    (equations : generated.equationAdmission = some true)
    (enabled : generated.logicFragment.core.modal = true)
    {parameters : ModalParameters checked.schema}
    (computed : generated.modalParameters? checked.schema = some parameters) :
    ∃ code, generated.annotatedModalFormer? checked inputs = some code ∧ code.1 = parameters.output := by
  unfold Generated.annotatedModalFormer?
  simp only [equations, enabled, and_self, ↓reduceIte]
  split
  · rename_i missing
    rw [computed] at missing
    contradiction
  · rename_i actual actualAt
    have same : actual = parameters := Option.some.inj (actualAt.symm.trans computed)
    subst actual
    exact ⟨_, rfl, rfl⟩

/-- Actual annotated formation still reads the computed modal output slot. -/
theorem annotated_modal_result_slot {generated : Generated} (checked : AnnotatedSchema generated)
    (inputs : ModalInputs checked.schema (generated.modalParameters? checked.schema))
    {code : Σ sort : HSort, TypeCode generated.plan checked.schema.focusBound checked.schema.focusCarrier sort}
    (formed : generated.annotatedModalFormer? checked inputs = some code) :
    ∃ assignment ∈ generated.sortAssignments,
      assignment.family.origin = .modal checked.schema.declaration.declarationIndex checked.schema.position ∧
      code.1 = assignment.output := by
  unfold Generated.annotatedModalFormer? at formed
  split at formed
  · split at formed
    · cases formed
    · rename_i parameters computed
      cases formed
      obtain ⟨assignment, member, origin, output, _⟩ := modal_parameters_origins computed
      exact ⟨assignment, member, origin, output⟩
  · cases formed

theorem annotated_modal_inhabitant_typed {generated : Generated} (checked : AnnotatedSchema generated)
    {code : Σ sort : HSort, TypeCode generated.plan checked.schema.focusBound checked.schema.focusCarrier sort}
    {term : Pattern} (inhabited : code.2.meaning term) :
    HasType generated.snapshot.language generated.snapshot.free checked.schema.focusBound term checked.schema.focusCarrier :=
  code.2.bounded term inhabited

end Mettapedia.OSLF.NativeTypes.Generation
