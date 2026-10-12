import Mettapedia.OSLF.NativeTypes.Generation.GuardedCenter
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardControls

open Mettapedia.OSLF.Framework

/-!
# Guarded formation changes the actual generated output

The same selected F/G language and sort profile are used in every case.
Only the actual provider changes. A complete empty guard admits the native
structural former; an enabling row rejects it; an undeclared query remains
unresolved. Uniform law checking retains its separate unresolved status.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.GuardControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardControls
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open ModalHypercube (HSort)

def snapshot (provider : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot) : Snapshot :=
  ⟨guardedTheory, [("x", .base "Term")], provider⟩

def fragment : LanguageFragment := {}
def chosen (provider : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot) :=
  selectedSnapshot (snapshot provider) fragment

def vertex (provider : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (chosen provider).language :=
  (fun _ => .star, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.separatedOutput (chosen provider).language)

def generated (provider : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot) : Generated :=
  generate (snapshot provider) fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment (vertex provider)

def first (provider : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot) :
    Fin (generated provider).snapshot.language.terms.length := ⟨0, by change 0 < 2; decide +kernel⟩

def inputs (provider : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot) :
    StructuralInputs (generated provider) [] (first provider) := fun position => {
      meaning term := HasType (generated provider).snapshot.language (generated provider).snapshot.free []
        term (structuralDeclaration (generated provider) (first provider)).params[position].typeExpr
      bounded _ inhabited := inhabited}

theorem same_generator_uniform_check_is_separate :
    (generated active).equationAdmission = none ∧ (generated inactive).equationAdmission = none := by
  decide +kernel

theorem guarded_check_consumes_actual_provider :
    (generated active).guardedEquationAdmission? = some false ∧
      (generated inactive).guardedEquationAdmission? = some true ∧
      (generated missing).guardedEquationAdmission? = none := by
  decide +kernel

theorem complete_empty_guard_forms_original_structural_code :
    ((generated inactive).guardedStructuralFormer? [] (first inactive) (inputs inactive)).isSome = true := by
  decide +kernel

theorem enabling_guard_rejects_original_structural_code :
    (generated active).guardedStructuralFormer? [] (first active) (inputs active) = none := by
  simp [Generated.guardedStructuralFormer?, (guarded_check_consumes_actual_provider).1]

theorem undeclared_guard_does_not_form_a_code :
    (generated missing).guardedStructuralFormer? [] (first missing) (inputs missing) = none := by
  exact unresolved_guard_has_no_structural_former _
    (guarded_check_consumes_actual_provider).2.2

theorem active_body_system_uses_actual_guard :
    (generated inactive).activeEquationBodies? = some [] ∧
      ((generated active).activeEquationBodies?).map List.length = some 1 := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.Generation.GuardControls
