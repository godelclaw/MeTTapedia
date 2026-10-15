import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeStructuralMeaning
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeSemanticControls

/-!
# Whole authored structural families and separating inhabitants

All constructors in the original lambda, partial-recursive machine and
two-sort nested-binder language use the same native graph construction.
The actual constructed result inhabits its fibre. A source variable cannot
inhabit a constructor's graph, regardless of its contextual arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage.Controls

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent
open IntrinsicScopedConditionalPresheaf Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSemanticAdmission

theorem lambda_all_structural_types (constructor : lambdaInstallation.Constructor) :
    (constructorModel lambdaInstallation lambdaSemantic).evaluateType
      ((constructorModel lambdaInstallation lambdaSemantic).termParameters constructor)
      (lambdaInstallation.structuralType constructor) =
      some (structuralNative lambdaInstallation lambdaSemantic constructor) :=
  structuralType_read lambdaInstallation lambdaSemantic constructor

theorem machine_all_structural_types (constructor : machineInstallation.Constructor) :
    (constructorModel machineInstallation machineSemantic).evaluateType
      ((constructorModel machineInstallation machineSemantic).termParameters constructor)
      (machineInstallation.structuralType constructor) =
      some (structuralNative machineInstallation machineSemantic constructor) :=
  structuralType_read machineInstallation machineSemantic constructor

theorem letCase_all_structural_types (constructor : letCaseInstallation.Constructor) :
    (constructorModel letCaseInstallation letCaseSemantic).evaluateType
      ((constructorModel letCaseInstallation letCaseSemantic).termParameters constructor)
      (letCaseInstallation.structuralType constructor) =
      some (structuralNative letCaseInstallation letCaseSemantic constructor) :=
  structuralType_read letCaseInstallation letCaseSemantic constructor

noncomputable def actual_structural_inhabitant {language : LanguageDef}
    (installed : NativeSignature.Installation language) (admitted : Admitted language)
    (constructor : installed.Constructor)
    (point : ((constructorModel installed admitted).termParameters constructor).1.Elements) :
    (structuralNative installed admitted constructor).decoded.obj point :=
  (structuralFibreEquiv installed admitted constructor point).symm
    ⟨((constructorModel installed admitted).termValue constructor).val point, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem source_variable_refused {language : LanguageDef}
    (installed : NativeSignature.Installation language) (admitted : Admitted language)
    (constructor : installed.Constructor)
    (arguments : (carrierScope installed.headers[constructor].parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone
        [language.terms[installed.origin constructor].category]))) :
    ¬ ∃ value : (structuralNative installed admitted constructor).decoded.obj
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone
          [language.terms[installed.origin constructor].category]), arguments⟩,
      (structuralTermFibreEquiv installed admitted constructor _ arguments value).val = Term.var Var.zero := by
  rintro ⟨value, equal⟩
  have graph := (structuralTermFibreEquiv installed admitted constructor _ arguments value).property
  rw [equal] at graph
  cases graph


end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage.Controls
