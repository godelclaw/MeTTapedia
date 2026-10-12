import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfTypeFormerTerms
import Mettapedia.TypeTheory.NativeLocalTypeDecoding

/-!
# Actual generated abstraction of an original dependent body

The body expression is independently authored in the original declaration
grammar, through its complete comprehension value. Its typing tree and
parser produce the actual native dependent abstraction. The complete body
comparison records every original source environment and witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafPi
open ContextualProductSections

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def dependentBodyTerm {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) : TermExpr (symbols K) 2 :=
  .primitive (.source body) (singletonArgument (comprehensionTerm A))

def dependentBodyTermFormed {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) :
    Derivation (signature K) (.term (sourceContext A) (dependentBodyTerm body) (dependentBodyType A B)) := by
  have tree := deriveList (.primitive (sourceContext A) (.source body)
    (singletonArgument (comprehensionTerm A)))
    (.cons (sourceContextFormed A) (.cons (objectContextFormed _)
      (.cons (sourceTypeFormed B)
        (.cons (objectArguments _ (sourceContextFormed A) (comprehensionTermFormed A)) .nil))))
  change Derivation (signature K) (.term (sourceContext A) (dependentBodyTerm body)
    ((sourceType B (.var 0)).substitute (singletonArgument (comprehensionTerm A)))) at tree
  have result : (sourceType B (.var 0)).substitute (singletonArgument (comprehensionTerm A)) =
      dependentBodyType A B := by
    change (TypeExpr.family (.source B) _ : TypeExpr (symbols K) 2) =
      (TypeExpr.family (.source B) _ : TypeExpr (symbols K) 2)
    congr 1
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible
  rw [result] at tree
  exact tree

def dependentBodyValue {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) : (dependentBodyMeaning A B).decoded.sections :=
  (NativeModel (Base K)).toCwf.tmSub (sourceValue body) (comprehensionMap A)

theorem dependent_body_term_read {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) :
    (model K).evaluateTerm (sourceScope A) (dependentBodyTerm body) =
      some ⟨dependentBodyMeaning A B, dependentBodyValue body⟩ := by
  exact (model K).evaluate_primitive (sourceScope A) (.source body)
    (singletonArgument (comprehensionTerm A)) (comprehensionMap A) (by
      intro position
      cases position using Fin.cases with
      | zero =>
        exact (comprehension_term_read A).trans
          (congrArg some (RepresentableIndexedDeclarations.forgetMap_component (displayArrow A))).symm
      | succ impossible => exact Fin.elim0 impossible)

def dependentLambdaTerm {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) : TermExpr (symbols K) 1 :=
  .lam (sourceType A (.var 0)) (dependentBodyType A B) (dependentBodyTerm body)

def dependentLambdaFormed {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) :
    Derivation (signature K) (.term (objectContext (⟨context⟩ : Base K))
      (dependentLambdaTerm body) (generatedProductType A B)) :=
  deriveList (.lambda (objectContext (⟨context⟩ : Base K))
    (sourceType A (.var 0)) (dependentBodyType A B) (dependentBodyTerm body))
    (.cons (sourceTypeFormed A) (.cons (dependentBodyFormed A B)
      (.cons (dependentBodyTermFormed body) .nil)))

theorem dependent_lambda_read {context : K.Ctx} {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) :
    (model K).evaluateTerm (objectScope (⟨context⟩ : Base K)) (dependentLambdaTerm body) =
      some ⟨generatedProductMeaning A B,
        (model K).products.lam (dependentBodyValue body)⟩ :=
  (model K).evaluate_lambda _ _ _ _ _ (source_type_read A) (dependent_body_read A B)
    _ _ (dependent_body_term_read body)

theorem dependent_body_value_complete {context : K.Ctx} {A : K.Ty context}
    {B : K.Ty (K.ext context A)} (body : K.Tm (K.ext context A) B) :
    HEq (dependentBodyValue body)
      (reindexDisplayedSection
        (totalReindexMap (objectName (⟨context⟩ : Base K)) (CwfYoneda.family K A))
        (CwfYoneda.dependentBodyFamily K A B)
        (CwfYoneda.representedBodySection K (A := A) (CwfYoneda.interpretTerm K body))) := by
  exact ContextualLocalUniverses.substituteTerm_heq
    (C := DisplayedPresheafCwf.presheafCwf (Base K))
    (type := sourceMeaning B) (sourceValue body) (comprehensionMap A)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
