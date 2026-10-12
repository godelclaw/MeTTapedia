import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison

/-!
# Authored curried constructors on contextual binder arguments

The actual source declaration selects the operation and every ordered scope.
The earned whole-context function comparison supplies its argument bodies.
Source application and capture-avoiding reindexing are read from the original
constructor family rather than supplied by language-specific interpreters.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open BindingFunctionArgumentComparison
open BindingSemanticAdmission

variable {language : LanguageDef}

noncomputable def sourceOperation (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    (origin : Fin language.terms.length) (context : List String)
    (arguments : FunctionArgs (algebra language)
      ((signature language).arity (originalOperator admitted origin)) context) :
    Source language context language.terms[origin.val].category :=
  sourceEquiv admitted labels context language.terms[origin.val].category
    (applyFunctionArgs (algebra language) (originalOperator admitted origin) arguments)

theorem operation_source_readout (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    (origin : Fin language.terms.length) (context : List String)
    (arguments : Args (signature language)
      ((signature language).arity (originalOperator admitted origin)) context) :
    (sourceOperation admitted labels origin context
      (toFunctions (algebra language) (FreeBindingTerms.syntaxToFamily arguments))).val =
      .apply language.terms[origin.val].label
        (toPatterns language.terms[origin.val].params arguments) := by
  change toPattern (applyFunctionArgs (algebra language) (originalOperator admitted origin)
    (toFunctions (algebra language) (FreeBindingTerms.syntaxToFamily arguments))) = _
  have roundTrip := fromFunctions_toFunctions (algebra language)
    (FreeBindingTerms.syntaxToFamily arguments)
  unfold applyFunctionArgs
  rw [roundTrip]
  change toPattern (.op (originalOperator admitted origin)
    (FreeBindingTerms.terms.familyToSyntax _ (FreeBindingTerms.syntaxToFamily arguments))) = _
  exact congrArg (fun values : Args (signature language)
    ((signature language).arity (originalOperator admitted origin)) context =>
      toPattern (.op (originalOperator admitted origin) values))
    (FreeBindingTerms.familyToSyntax_syntaxToFamily arguments)

/-- Ambient substitution lifts under every computed original parameter scope,
and applying the constructor commutes with that exact substitution. -/
theorem operation_substitution (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    (origin : Fin language.terms.length) {context target : List String}
    (substitution : Sub (signature language) context target)
    (arguments : FunctionArgs (algebra language)
      ((signature language).arity (originalOperator admitted origin)) context) :
    sourceOperation admitted labels origin target
      (FunctionArgs.reindex (algebra language) substitution arguments) =
    sourceEquiv admitted labels target language.terms[origin.val].category
      (Binding.bind substitution
        (applyFunctionArgs (algebra language) (originalOperator admitted origin) arguments)) := by
  apply congrArg (sourceEquiv admitted labels target language.terms[origin.val].category)
  exact applyFunctionArgs_substitute (algebra language) substitution
    (originalOperator admitted origin) arguments

/-- Native installation and the binding interpretation use the same original
authored declaration, including binder names and ordered parameter metadata. -/
theorem installed_operator_source (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor) :
    (originalOperator admitted (installed.origin constructor)).index = installed.origin constructor := rfl

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
