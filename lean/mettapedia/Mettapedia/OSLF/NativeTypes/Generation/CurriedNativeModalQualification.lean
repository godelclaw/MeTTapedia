import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualInterpretation

/-!
# A genuine contextual interpretation target for authored native events

The common source model's concrete dependent evaluator is compared with the
generic contextual evaluator. Actual native logical operations and their
substitution, beta and eta laws then qualify this model as a target of the
free generated contextual grammar. Primitive meanings remain unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent
open CurriedBindingLanguage BindingSemanticAdmission

variable {plan : Plan} {modal : List (NativeModalHeaders.Header plan)}

variable (installed : NativeSignature.Installation plan.snapshot.language)
    (admitted : Admitted plan.snapshot.language) (diagram : Diagram plan modal)

noncomputable def qualifiedModel :
    Refinement.Contextual.Interpretation.QualifiedModel
      (NativeModalSignature.signature plan installed modal)
      (Refinement.NativeModel (Worlds plan.snapshot.language)) where
  localModel := PresheafNativePredicateModel.model (Worlds plan.snapshot.language)
  data := (model installed admitted diagram).toAbstract
  realization := (realization installed admitted diagram).toAbstract
  products_substitution := (PresheafNativePredicateModel.qualification (Worlds plan.snapshot.language)).stableProducts
  products_beta := (PresheafNativePredicateModel.qualification (Worlds plan.snapshot.language)).productBeta
  products_eta := (PresheafNativePredicateModel.qualification (Worlds plan.snapshot.language)).productEta

theorem qualified_type_read {n : Nat} (scope : Refinement.Scope (Worlds plan.snapshot.language) n)
    (type : Refinement.TypeExpr (NativeModalSignature.symbols plan installed modal) n) :
    (qualifiedModel installed admitted diagram).data.evaluateType
      (Refinement.NativeAbstractScope.toGeneric scope) type =
      (model installed admitted diagram).evaluateType scope type :=
  (model installed admitted diagram).evaluateType_compare type scope

theorem qualified_term_read {n : Nat} (scope : Refinement.Scope (Worlds plan.snapshot.language) n)
    (term : Refinement.TermExpr (NativeModalSignature.symbols plan installed modal) n) :
    (qualifiedModel installed admitted diagram).data.evaluateTerm
      (Refinement.NativeAbstractScope.toGeneric scope) term =
      (model installed admitted diagram).evaluateTerm scope term :=
  (model installed admitted diagram).evaluateTerm_compare term scope

theorem qualified_predicate_read {n : Nat} (scope : Refinement.Scope (Worlds plan.snapshot.language) n)
    (predicate : Refinement.PropExpr (NativeModalSignature.symbols plan installed modal) n) :
    (qualifiedModel installed admitted diagram).data.evaluatePredicate
      (Refinement.NativeAbstractScope.toGeneric scope) predicate =
      (model installed admitted diagram).evaluatePredicate scope predicate :=
  (model installed admitted diagram).evaluatePredicate_compare predicate scope

theorem qualified_context_read {n : Nat}
    (context : Refinement.ContextExpr (NativeModalSignature.symbols plan installed modal) n) :
    (qualifiedModel installed admitted diagram).data.evaluateContext context =
      ((model installed admitted diagram).evaluateContext context).map Refinement.NativeAbstractScope.toGeneric :=
  (model installed admitted diagram).evaluateContext_compare context

end Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel
