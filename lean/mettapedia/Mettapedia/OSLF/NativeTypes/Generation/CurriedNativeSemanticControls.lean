import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeSourceFibres
import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmissionControls

/-!
# Original authored native-model consumers and separating controls

Each original presentation uses the same generated installation and native
model. The contracts quantify over every installed declaration and context.
Nested binder parameters, named free variables and unequal raw metadata
exercise the independent source comparison rather than a language adapter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage.Controls

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.TypeTheory.Calculi.NativeDependent
open BindingSemanticAdmission
open BindingCarrierSemantics (FreeDeclarations)

abbrev originalLambda := Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
abbrev originalMachine := Mettapedia.Languages.PartrecMachine.partrecMachine
abbrev originalLetCase := Mettapedia.OSLF.NativeTypes.Instances.LetCase.language

def lambdaInstallation : NativeSignature.Installation originalLambda :=
  (NativeSignature.install? originalLambda).get (by decide)

def machineInstallation : NativeSignature.Installation originalMachine :=
  (NativeSignature.install? originalMachine).get (by decide)

def letCaseInstallation : NativeSignature.Installation originalLetCase :=
  (NativeSignature.install? originalLetCase).get (by decide)

theorem lambdaSemantic : Admitted originalLambda :=
  (check_exact _).mp BindingSemanticAdmission.Controls.original_lambda_admitted

theorem machineSemantic : Admitted originalMachine :=
  (check_exact _).mp BindingSemanticAdmission.Controls.original_machine_admitted

theorem letCaseSemantic : Admitted originalLetCase :=
  (check_exact _).mp BindingSemanticAdmission.Controls.original_letCase_admitted

theorem lambdaLabels : (originalLambda.terms.map (·.label)).Nodup := by decide
theorem machineLabels : (originalMachine.terms.map (·.label)).Nodup := by decide
theorem letCaseLabels : (originalLetCase.terms.map (·.label)).Nodup := by decide

/-- Every original lambda constructor, including its binding parameter,
is realized by the actual native dependent evaluator. -/
theorem lambda_all_headers_realized :
    Refinement.SignatureRealization (constructorModel lambdaInstallation lambdaSemantic)
      lambdaInstallation.signature :=
  constructorModel_realization lambdaInstallation lambdaSemantic

theorem machine_all_headers_realized :
    Refinement.SignatureRealization (constructorModel machineInstallation machineSemantic)
      machineInstallation.signature :=
  constructorModel_realization machineInstallation machineSemantic

theorem letCase_all_headers_realized :
    Refinement.SignatureRealization (constructorModel letCaseInstallation letCaseSemantic)
      letCaseInstallation.signature :=
  constructorModel_realization letCaseInstallation letCaseSemantic

noncomputable def lambda_native_sources (P : IntrinsicScopedConditionalPresheaf.Base (algebra originalLambda) ⥤ Type)
    (position : Fin originalLambda.types.length) (context : List String)
    (point : P.obj (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
      (algebra originalLambda).substitution.toClone context))) :=
  nativeSortSourceEquiv lambdaSemantic lambdaLabels P position context point

noncomputable def machine_native_sources (P : IntrinsicScopedConditionalPresheaf.Base (algebra originalMachine) ⥤ Type)
    (position : Fin originalMachine.types.length) (context : List String)
    (point : P.obj (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
      (algebra originalMachine).substitution.toClone context))) :=
  nativeSortSourceEquiv machineSemantic machineLabels P position context point

noncomputable def letCase_native_sources (P : IntrinsicScopedConditionalPresheaf.Base (algebra originalLetCase) ⥤ Type)
    (position : Fin originalLetCase.types.length) (context : List String)
    (point : P.obj (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
      (algebra originalLetCase).substitution.toClone context))) :=
  nativeSortSourceEquiv letCaseSemantic letCaseLabels P position context point

def caseCarrier : NativeSignature.Carrier originalLetCase :=
  .function (.sort ⟨0, by decide⟩)
    (.function (.sort ⟨0, by decide⟩) (.sort ⟨1, by decide⟩))

theorem caseParameterDecoded :
    NativeSignature.decodeParameter? originalLetCase originalLetCase.terms[4].params[1] =
      some caseCarrier := by decide

theorem caseParameterMeaning :
    ParameterMeaning originalLetCase.terms[4].params[1] ["Value", "Value"] "Computation" :=
  (parameterMeaning?_exact _ _ _).mp (by decide)

/-- The actual native iterated Pi parameter has exactly the independently
typed two-binder computation bodies at every ambient context. -/
noncomputable def case_native_bodies (P : IntrinsicScopedConditionalPresheaf.Base (algebra originalLetCase) ⥤ Type)
    (context : List String)
    (point : P.obj (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
      (algebra originalLetCase).substitution.toClone context))) :=
  nativeParameterSourceEquiv letCaseSemantic letCaseLabels P caseParameterMeaning
    caseCarrier caseParameterDecoded context point

def namedLambda (name : String) : AuthoredSource originalLambda [] [] "Term" :=
  ⟨.apply "Lam" [.lambda (some name) (.bvar 0)],
    ⟨.apply "Lam" [.lambda none (.bvar 0)], checkHasType_sound (by decide), by simp [Pattern.AlphaEquiv, Pattern.eraseBinderMetadata]⟩, rfl⟩

noncomputable def leftReceipt := authoredReceipt lambdaSemantic lambdaLabels [] [] "Term" (namedLambda "left")
noncomputable def rightReceipt := authoredReceipt lambdaSemantic lambdaLabels [] [] "Term" (namedLambda "right")

theorem named_metadata_same_meaning : leftReceipt.term = rightReceipt.term :=
  alpha_sources_equal_semantic_terms lambdaSemantic lambdaLabels [] [] "Term"
    (namedLambda "left") (namedLambda "right")
      (by simp [namedLambda, Pattern.AlphaEquiv, Pattern.eraseBinderMetadata])

theorem named_metadata_distinct_receipts : leftReceipt ≠ rightReceipt :=
  original_metadata_distinguishes_receipts leftReceipt rightReceipt (by decide)

def declaredFree : FreeDeclarations := [("external", "Term")]

def freeLambda : AuthoredSource originalLambda declaredFree [] "Term" :=
  ⟨.apply "Lam" [.lambda (some "bound") (.fvar "external")],
    ⟨.apply "Lam" [.lambda none (.fvar "external")], checkHasType_sound (by decide), by simp [Pattern.AlphaEquiv, Pattern.eraseBinderMetadata]⟩, rfl⟩

theorem free_context_exact_readback :
    BindingCarrierSemantics.openFree 0 declaredFree
      (toPattern (encodeAuthored lambdaSemantic lambdaLabels declaredFree [] "Term" freeLambda)) =
      .apply "Lam" [.lambda none (.fvar "external")] := by
  simpa only [freeLambda, Pattern.eraseBinderMetadata, List.map_cons, List.map_nil,
    List.length_nil] using
    encodeAuthored_readback lambdaSemantic lambdaLabels declaredFree [] "Term" freeLambda

theorem ordinary_arrow_headers_form_but_meaning_refused :
    (NativeSignature.install? BindingCarrierSemantics.ArrowCounterexample.language).isSome = true ∧
      check BindingCarrierSemantics.ArrowCounterexample.language = false :=
  ⟨BindingCarrierSemantics.ArrowCounterexample.native_headers_admitted,
    BindingSemanticAdmission.Controls.ordinary_arrow_refused⟩

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage.Controls
