import Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations

/-!
# Original authored constructors on contextual function arguments

The operator retains its entire authored declaration, including parameter
names and binder metadata. Its actual contextual function arguments are
converted through the earned binding comparison. Constructor application and
ambient substitution commute, with the original source pattern as readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Poly.BindingLanguage
open BindingFunctionArgumentComparison
open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf MultiBinderPresheaf

variable {language : LanguageDef}

theorem parameter_is_single (parameter : TermParam)
    (supported : supportedParameter parameter = true) :
    (multiBase? parameter).isNone := by
  cases parameter with
  | simple => rfl
  | abstractionNamed => rfl
  | multiAbstractionNamed => simp [supportedParameter] at supported

/-- Every operator is computed from the original declaration position.
Nothing discards its source binder names or invents an independent arity. -/
def authoredOperator (checked : checkProfile language = true)
    (origin : Fin language.terms.length) :
    (signature language).Op language.terms[origin.val].category := by
  have parametersChecked :
      language.terms.all (fun declaration => declaration.params.all supportedParameter) = true := by
    simp only [checkProfile, Bool.and_eq_true] at checked
    exact checked.1
  exact
  ⟨⟨language.terms[origin.val], List.getElem_mem origin.isLt,
      (profile_sound language checked).1 _ (List.getElem_mem origin.isLt), rfl⟩,
    plainOccurrence language.terms[origin.val].params (fun parameter member =>
      parameter_is_single parameter
        (List.all_eq_true.mp
          (List.all_eq_true.mp parametersChecked _
            (List.getElem_mem origin.isLt)) parameter member))⟩

theorem operator_source (checked : checkProfile language = true)
    (origin : Fin language.terms.length) :
    (authoredOperator checked origin).1.1 = language.terms[origin.val] := rfl

theorem installed_operator_source (installed : NativeSignature.Installation language)
    (checked : checkProfile language = true) (constructor : installed.Constructor) :
    (authoredOperator checked (installed.origin constructor)).1.1 =
      language.terms[(installed.origin constructor).val] := rfl

/-- Interpretation of a source constructor by the actual binding clone,
followed by independent authored typing and source readout. -/
noncomputable def sourceOperation (checked : checkProfile language = true)
    (origin : Fin language.terms.length) (context : List String)
    (arguments : FunctionArgs (algebra language)
      ((signature language).arity (authoredOperator checked origin)) context) :
    TypedObject language context language.terms[origin.val].category :=
  sourceEquiv (profile_sound language checked).1 (profile_sound language checked).2
    context language.terms[origin.val].category
    (applyFunctionArgs (algebra language) (authoredOperator checked origin) arguments)

/-- The contextual interpretation returns exactly the original authored
constructor and its ordered printed argument spine. -/
theorem operation_source_readout (checked : checkProfile language = true)
    (origin : Fin language.terms.length) (context : List String)
    (arguments : Args (signature language)
      ((signature language).arity (authoredOperator checked origin)) context) :
    (sourceOperation checked origin context
      (toFunctions (algebra language) (FreeBindingTerms.syntaxToFamily arguments))).val =
      .apply language.terms[origin.val].label
        (patternsOfDecl language.terms[origin.val].params
          (authoredOperator checked origin).2.counts
          ((signature language).arity (authoredOperator checked origin)) arguments) := by
  change toPattern (applyFunctionArgs (algebra language) (authoredOperator checked origin)
    (toFunctions (algebra language) (FreeBindingTerms.syntaxToFamily arguments))) = _
  have roundTrip := fromFunctions_toFunctions (algebra language)
    (FreeBindingTerms.syntaxToFamily arguments)
  unfold applyFunctionArgs
  rw [roundTrip]
  change toPattern (.op (authoredOperator checked origin)
    (FreeBindingTerms.terms.familyToSyntax _ (FreeBindingTerms.syntaxToFamily arguments))) = _
  rw [FreeBindingTerms.familyToSyntax_syntaxToFamily]
  rfl

/-- Reindexing contextual function arguments is exactly the authored
capture-avoiding substitution of the resulting constructor term. -/
theorem operation_substitution (checked : checkProfile language = true)
    (origin : Fin language.terms.length) {context target : List String}
    (substitution : Sub (signature language) context target)
    (arguments : FunctionArgs (algebra language)
      ((signature language).arity (authoredOperator checked origin)) context) :
    sourceOperation checked origin target
      (FunctionArgs.reindex (algebra language) substitution arguments) =
      sourceEquiv (profile_sound language checked).1 (profile_sound language checked).2
        target language.terms[origin.val].category
        (Binding.bind substitution
          (applyFunctionArgs (algebra language) (authoredOperator checked origin) arguments)) := by
  apply congrArg (sourceEquiv (profile_sound language checked).1
    (profile_sound language checked).2 target language.terms[origin.val].category)
  exact applyFunctionArgs_substitute (algebra language) substitution
    (authoredOperator checked origin) arguments

/-- Yoneda reindexing opens the same source body as lifting the actual
substitution beneath the original binder. -/
theorem function_body_substitution
    (fragment : ∀ declaration ∈ language.terms, BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup)
    {context target : List String}
    (substitution : Sub (signature language) context target)
    (domain codomain : Fin language.types.length)
    (function : (meaning (.function (.sort domain) (.sort codomain))).obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    (functionBodyEquiv fragment labels target domain codomain
      ((meaning (.function (.sort domain) (.sort codomain))).map
        (Opposite.op (environmentArrow (algebra language) substitution)) function)).val =
      toPattern (Binding.bind (liftSub substitution [language.types[domain.val].name])
        (scopedBodyEquiv (algebra language)
          (ContextObject.ofList (algebra language).substitution.toClone context)
          [language.types[domain.val].name] language.types[codomain.val].name function)) := by
  let scope := [language.types[domain.val].name]
  let result := language.types[codomain.val].name
  let sourceContext := ContextObject.ofList (algebra language).substitution.toClone context
  let targetContext := ContextObject.ofList (algebra language).substitution.toClone target
  let arrow := environmentArrow (algebra language) substitution
  change toPattern (scopedBodyEquiv (algebra language) targetContext scope result
    (((binders (algebra language) scope).functorHom (programs (algebra language) result)).map
      (Opposite.op arrow) function)) = _
  have reindexed := scopedBodyEquiv_reindex (algebra language) scope result
    (Opposite.op arrow) function
  have extended := extendScope_environment (algebra language) scope substitution
  change extendScope (algebra language) scope (Quiver.Hom.unop (Opposite.op arrow)) =
    environmentArrow (algebra language)
      ((algebra language).substitution.liftEnvironment substitution scope) at extended
  rw [extended] at reindexed
  have bodySubstitution :
      (algebra language).substitution.toClone.substitute
        (scopedBodyEquiv (algebra language) sourceContext scope result function)
        (environmentArrow (algebra language)
          ((algebra language).substitution.liftEnvironment substitution scope)) =
      Binding.bind (liftSub substitution scope)
        (scopedBodyEquiv (algebra language) sourceContext scope result function) := by
    change Binding.bind (fromPositions (F := Term (signature language)) (scope ++ context)
      (environmentArrow (algebra language)
        ((algebra language).substitution.liftEnvironment substitution scope))) _ = _
    congr 1
    funext sort v
    exact (fromPositions_ofEnvironment
      ((algebra language).substitution.liftEnvironment substitution scope) v).trans
      (congrFun (congrFun (terms_liftEnvironment_eq_liftSub substitution scope) sort) v)
  exact congrArg toPattern (reindexed.trans bodySubstitution)

end Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
