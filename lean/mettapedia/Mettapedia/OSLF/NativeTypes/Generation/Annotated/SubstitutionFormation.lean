import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Checking
import Mettapedia.OSLF.NativeTypes.Generation.Annotated.SubstitutionControls

open Mettapedia.OSLF.Framework

/-!
# Generated modal codes for explicit substitution families

The intermediate arrow type and complete two-binder focus context are checked
by the annotated generator before formation. Native parameters are obtained
from the original authored position, and the continuation denotes properly
sorted programs at the supplied source type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Annotated.SubstitutionFormation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation
open Mettapedia.OSLF.NativeTypes.Generation.Annotated.SubstitutionControls

theorem equation_admitted : generated.equationAdmission = some true := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws chosen.language
      (selectedEquationLaws chosen.language permissions)) vertex.2 = some true
  have empty : chosen.language.equations = [] := by
    rw [chosen_snapshot]
    rfl
  have noLaws : selectedEquationLaws chosen.language permissions = [] := by
    simp [selectedEquationLaws, Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws, empty]
  rw [noLaws]
  rfl

theorem focus_rely_empty (domain leaf : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 2 (annotation domain leaf bound) = .ok checked) :
    checked.schema.relyNames = [] := by
  have retained := instantiated_schema_input_retained produced
  have actualAt := checked.source.present
  rw [retained.1, actual_bound_template] at actualAt
  have same := Option.some.inj actualAt.symm
  unfold Schema.relyNames
  change RedexPosition.relyVars checked.schema.declaration.authored.left checked.schema.position = []
  rw [checked.original_authored]
  change RedexPosition.relyVars checked.source.site.rule.left checked.source.site.position = []
  rw [same]
  rfl

def parameters (checked : AnnotatedSchema generated) : ModalParameters checked.schema :=
  (generated.modalParameters? checked.schema).get (by
    exact Option.isSome_iff_exists.mpr
      (generated_annotated_parameters_complete snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex checked))

theorem parameters_computed (checked : AnnotatedSchema generated) :
    generated.modalParameters? checked.schema = some (parameters checked) :=
  (Option.some_get _).symm

def continuationCode (checked : AnnotatedSchema generated) (_assignment : ScopedRuleMatching.Assignment) :
    TypeCode generated.plan checked.schema.bound checked.schema.programCarrier (parameters checked).output where
  meaning result := checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    checked.schema.bound checked.schema.programCarrier result = true
  bounded _ accepted := (checkOpenPatternWellSorted_sound accepted).1

def relyCodes (domain leaf : TypeExpr) (bound : List TypeExpr) (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 2 (annotation domain leaf bound) = .ok checked) :
    RelyCodes checked.schema (parameters checked).inputs := fun name => by
  have absent := name.property
  simp only [focus_rely_empty domain leaf bound checked produced, List.not_mem_nil] at absent

def codes (domain leaf : TypeExpr) (bound : List TypeExpr) (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 2 (annotation domain leaf bound) = .ok checked) :
    ModalInstanceCodes generated checked.schema :=
  ⟨parameters checked, parameters_computed checked,
    relyCodes domain leaf bound checked produced, continuationCode checked⟩

theorem every_substitution_modal_code_formed (domain leaf : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 2 (annotation domain leaf bound) = .ok checked) :
    ∃ code, generated.annotatedModalFormer? checked (codes domain leaf bound checked produced).actualInputs = some code ∧
      ∃ assignment ∈ generated.sortAssignments,
        assignment.family.origin = .modal checked.schema.declaration.declarationIndex checked.schema.position ∧
        code.1 = assignment.output :=
  generated_annotated_m_form snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex checked
    equation_admitted rfl (codes domain leaf bound checked produced).actualInputs

end Mettapedia.OSLF.NativeTypes.Generation.Annotated.SubstitutionFormation
