import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceExtension
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualInterpretation

/-!
# Contextual interpretation of source-preserving cube enrichment

The computed source, cube and injection declarations share the concrete native
presheaf evaluator. Its full dependent interpretation and logical operations
qualify this actual model as a target of the free contextual grammar.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceExtension

open _root_.CategoryTheory
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent

universe u
variable {S : Refinement.Symbols} {D : CubeEnrichment.Signature}
    {W : Type u} [Category.{u} W] {bound : Nat}
variable (source : Refinement.Signature S)
    (carriers : CubeNativeExtension.SourceCarriers source D bound)
    (sourceModel : Refinement.ModelData S W)
    (realized : Refinement.SignatureRealization sourceModel source)
    (vertex : CubeEnrichment.Vertex D) (positive : 0 < bound)

noncomputable def qualifiedModel :
    Refinement.Contextual.Interpretation.QualifiedModel
      (CubeNativeExtension.signature source vertex bound carriers positive)
      (Refinement.NativeModel W) where
  localModel := PresheafNativePredicateModel.model W
  data := (model source carriers sourceModel realized vertex).toAbstract
  realization := (realization source carriers sourceModel realized vertex positive).toAbstract
  products_substitution := (PresheafNativePredicateModel.qualification W).stableProducts
  products_beta := (PresheafNativePredicateModel.qualification W).productBeta
  products_eta := (PresheafNativePredicateModel.qualification W).productEta

theorem qualified_type_read {n : Nat} (scope : Refinement.Scope W n)
    (type : Refinement.TypeExpr (CubeNativeExtension.symbols S D) n) :
    (qualifiedModel source carriers sourceModel realized vertex positive).data.evaluateType
      (Refinement.NativeAbstractScope.toGeneric scope) type =
      (model source carriers sourceModel realized vertex).evaluateType scope type :=
  (model source carriers sourceModel realized vertex).evaluateType_compare type scope

theorem qualified_term_read {n : Nat} (scope : Refinement.Scope W n)
    (term : Refinement.TermExpr (CubeNativeExtension.symbols S D) n) :
    (qualifiedModel source carriers sourceModel realized vertex positive).data.evaluateTerm
      (Refinement.NativeAbstractScope.toGeneric scope) term =
      (model source carriers sourceModel realized vertex).evaluateTerm scope term :=
  (model source carriers sourceModel realized vertex).evaluateTerm_compare term scope

theorem qualified_predicate_read {n : Nat} (scope : Refinement.Scope W n)
    (predicate : Refinement.PropExpr (CubeNativeExtension.symbols S D) n) :
    (qualifiedModel source carriers sourceModel realized vertex positive).data.evaluatePredicate
      (Refinement.NativeAbstractScope.toGeneric scope) predicate =
      (model source carriers sourceModel realized vertex).evaluatePredicate scope predicate :=
  (model source carriers sourceModel realized vertex).evaluatePredicate_compare predicate scope

theorem qualified_context_read {n : Nat}
    (context : Refinement.ContextExpr (CubeNativeExtension.symbols S D) n) :
    (qualifiedModel source carriers sourceModel realized vertex positive).data.evaluateContext context =
      ((model source carriers sourceModel realized vertex).evaluateContext context).map
        Refinement.NativeAbstractScope.toGeneric :=
  (model source carriers sourceModel realized vertex).evaluateContext_compare context

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceExtension
