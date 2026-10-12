import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.ActiveSystem
import Mettapedia.OSLF.NativeTypes.Generation.ModalCodes
import Mettapedia.OSLF.NativeTypes.Generation.StructuralCodes

open Mettapedia.OSLF.Framework

/-!
# Provider-relative law admission through the executable generator

The selected snapshot, provider, declaration streams and generated profile
are the existing generator's actual fields. Guarded admission is distinct
from its uniform source-law admission. The guarded formation methods use
the same catalogue, computed coordinates and semantic type formers; they
add no alternative handwritten schemas or structural operators.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource
open Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation
open ModalHypercube (HSort)

def Generated.guardedEquationAdmission? (generated : Generated) : Option Bool :=
  checkLaws? generated.snapshot.language generated.snapshot.provider generated.vertex.2
    (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational)

def Generated.guardedRewriteAdmission? (generated : Generated) : Option Bool :=
  checkLaws? generated.snapshot.language generated.snapshot.provider generated.vertex.2
    (selectedRewriteLaws generated.snapshot.language generated.languageFragment.operational)

theorem generated_guarded_equations_exact (generated : Generated) :
    generated.guardedEquationAdmission? = some true ↔
      ∀ equation index, (equation, index) ∈ generated.snapshot.language.equations.zipIdx →
        selected generated.languageFragment.operational.equationIndices index = true →
        generated.languageFragment.operational.equationDirections.isEmpty = false →
          SourceAdmitted generated.snapshot.language generated.snapshot.provider generated.vertex.2
            (equationLaw equation index) := by
  rw [Generated.guardedEquationAdmission?, laws_check_exact]
  constructor
  · intro accepted equation index original selectedIndex directions
    exact accepted _ ((selected_equation_law_iff _ _ _).mpr
      ⟨(equation_law_origin _ _).mpr ⟨equation, index, original, rfl⟩, selectedIndex, directions⟩)
  · intro accepted law original
    obtain ⟨source, selectedIndex, directions⟩ := (selected_equation_law_iff _ _ _).mp original
    obtain ⟨equation, index, declared, rfl⟩ := (equation_law_origin _ _).mp source
    exact accepted equation index declared selectedIndex directions

theorem generated_guarded_rewrites_exact (generated : Generated) :
    generated.guardedRewriteAdmission? = some true ↔
      ∀ rule index, (rule, index) ∈ generated.snapshot.language.rewrites.zipIdx →
        selected generated.languageFragment.operational.ruleIndices index = true →
          SourceAdmitted generated.snapshot.language generated.snapshot.provider generated.vertex.2
            (rewriteLaw rule index) := by
  rw [Generated.guardedRewriteAdmission?, laws_check_exact]
  constructor
  · intro accepted rule index original selectedIndex
    exact accepted _ ((selected_rewrite_law_iff _ _ _).mpr
      ⟨(rewrite_law_origin _ _).mpr ⟨rule, index, original, rfl⟩, selectedIndex⟩)
  · intro accepted law original
    obtain ⟨source, selectedIndex⟩ := (selected_rewrite_law_iff _ _ _).mp original
    obtain ⟨rule, index, declared, rfl⟩ := (rewrite_law_origin _ _).mp source
    exact accepted rule index declared selectedIndex

def Generated.activeEquationBodies? (generated : Generated) :
    Option (List (Equation (signature generated.snapshot.language))) :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.ActiveSystem.activeEquations? generated.snapshot.language generated.snapshot.provider
    (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational)

theorem generated_active_body_exact (generated : Generated)
    (bodies : List (Equation (signature generated.snapshot.language)))
    (computed : generated.activeEquationBodies? = some bodies)
    (body : Equation (signature generated.snapshot.language)) :
    body ∈ bodies ↔ ∃ equation index,
      (equation, index) ∈ generated.snapshot.language.equations.zipIdx ∧
        selected generated.languageFragment.operational.equationIndices index = true ∧
        generated.languageFragment.operational.equationDirections.isEmpty = false ∧
        ∃ guards, guards? generated.snapshot.provider equation.premises = some guards ∧
          enabled guards = true ∧
          encodeLaw generated.snapshot.language (bodyLaw (equationLaw equation index)) = some body := by
  rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.ActiveSystem.active_equation_origin _ _ _ _ computed]
  constructor
  · rintro ⟨law, original, guards, guardRead, active, encoded⟩
    obtain ⟨source, selectedIndex, directions⟩ := (selected_equation_law_iff _ _ _).mp original
    obtain ⟨equation, index, declared, rfl⟩ := (equation_law_origin _ _).mp source
    exact ⟨equation, index, declared, selectedIndex, directions, guards, guardRead, active, encoded⟩
  · rintro ⟨equation, index, declared, selectedIndex, directions, guards, guardRead, active, encoded⟩
    exact ⟨equationLaw equation index, (selected_equation_law_iff _ _ _).mpr
      ⟨(equation_law_origin _ _).mpr ⟨equation, index, declared, rfl⟩, selectedIndex, directions⟩,
      guards, guardRead, active, encoded⟩

theorem generated_guarded_display_quotient (generated : Generated)
    (bodies : List (Equation (signature generated.snapshot.language)))
    (computed : generated.activeEquationBodies? = some bodies)
    (accepted : generated.guardedEquationAdmission? = some true)
    (valuation : Nat → HSort) (first second : Term (signature generated.snapshot.language))
    (equivalent : TypedDisplayConvertibility generated.vertex.2 ⟨bodies⟩ valuation first second) :
    displaySort generated.vertex.2 valuation first = displaySort generated.vertex.2 valuation second :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.ActiveSystem.active_typed_quotient_readout _ _ _ _ _ computed accepted
    valuation first second equivalent

def Generated.guardedModalFormer? (generated : Generated) (schema : Schema generated.plan)
    (inputs : ModalInputs schema (generated.modalParameters? schema)) :
    Option (Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort) :=
  if generated.guardedEquationAdmission? = some true ∧ generated.logicFragment.core.modal = true ∧
      generated.schemaAdmitted? schema = true then
    match parameters : generated.modalParameters? schema with
    | none => none
    | some profile =>
        let supplied : ModalInputs schema (some profile) := parameters ▸ inputs
        some ⟨profile.output,
          generatedFormer schema profile.inputs profile.output profile.output supplied.1 supplied.2⟩
  else none

theorem guarded_modal_uses_original_catalogue {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    {code : Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort}
    (formed : generated.guardedModalFormer? schema inputs = some code) :
    schema ∈ generated.modalCatalogue ∧ generated.guardedEquationAdmission? = some true ∧
      generated.logicFragment.core.modal = true := by
  unfold Generated.guardedModalFormer? at formed
  split at formed
  · rename_i admitted
    exact ⟨(schema_admitted_iff _ _).mp admitted.2.2, admitted.1, admitted.2.1⟩
  · cases formed

theorem guarded_modal_exact_former {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    {code : Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort}
    (formed : generated.guardedModalFormer? schema inputs = some code) :
    ∃ profile, ∃ parameters : generated.modalParameters? schema = some profile,
      code = ⟨profile.output, generatedFormer schema profile.inputs profile.output profile.output
        (parameters ▸ inputs).1 (parameters ▸ inputs).2⟩ := by
  unfold Generated.guardedModalFormer? at formed
  split at formed
  · split at formed
    · cases formed
    · rename_i profile parameters
      exact ⟨profile, parameters, (Option.some.inj formed).symm⟩
  · cases formed

theorem guarded_modal_formation {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    {code : Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort}
    (formed : generated.guardedModalFormer? schema inputs = some code) {term : Pattern}
    (inhabited : code.2.meaning term) :
    schema ∈ generated.modalCatalogue ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.HasType generated.snapshot.language generated.snapshot.free
        schema.focusBound term schema.focusCarrier :=
  ⟨(guarded_modal_uses_original_catalogue inputs formed).1, code.2.bounded term inhabited⟩

def Generated.guardedStructuralFormer? (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) :
    Option (Σ sort : HSort,
      TypeCode generated.plan bound (.base (structuralDeclaration generated index).category) sort) :=
  if generated.guardedEquationAdmission? = some true ∧
      (⟨index.val, structuralDeclaration generated index⟩ : Mettapedia.OSLF.NativeTypes.Structural.Former) ∈
        generated.structuralCatalogue then
    some ⟨structuralOutputSort generated index, structuralCode generated bound index inputs⟩
  else none

theorem guarded_structural_exact_former {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} (inputs : StructuralInputs generated bound index)
    {code : Σ sort : HSort,
      TypeCode generated.plan bound (.base (structuralDeclaration generated index).category) sort}
    (formed : generated.guardedStructuralFormer? bound index inputs = some code) :
    generated.guardedEquationAdmission? = some true ∧
      (⟨index.val, structuralDeclaration generated index⟩ : Mettapedia.OSLF.NativeTypes.Structural.Former) ∈
        generated.structuralCatalogue ∧
      code = ⟨structuralOutputSort generated index, structuralCode generated bound index inputs⟩ := by
  unfold Generated.guardedStructuralFormer? at formed
  split at formed
  · rename_i admitted
    exact ⟨admitted.1, admitted.2, (Option.some.inj formed).symm⟩
  · cases formed

theorem unresolved_guard_has_no_structural_former {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} (inputs : StructuralInputs generated bound index)
    (unresolved : generated.guardedEquationAdmission? = none) :
    generated.guardedStructuralFormer? bound index inputs = none := by
  simp [Generated.guardedStructuralFormer?, unresolved]

end Mettapedia.OSLF.NativeTypes.Generation
