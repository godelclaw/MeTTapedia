import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfSubstitution
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedForgetSubstitution

/-!
# Dependent generated bodies over original comprehension values

The existing indexed-value declaration returns the complete original
comprehension value. A dependent source body is applied to that value,
retaining both its original environment and its supplied witness. The raw
sum and product expressions have independent typing trees and actual native
readouts in the same generated declaration signature.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def comprehensionTerm {context : K.Ctx} (A : K.Ty context) : TermExpr (symbols K) 2 :=
  .primitive (.forget A) TermExpr.var

def comprehensionTermFormed {context : K.Ctx} (A : K.Ty context) :
    Derivation (signature K) (.term (sourceContext A) (comprehensionTerm A)
      (objectType (⟨K.ext context A⟩ : Base K) 2)) := by
  have tree := deriveList (.primitive (sourceContext A) (.forget A) TermExpr.var)
    (.cons (sourceContextFormed A) (.cons (sourceContextFormed A)
      (.cons ((headers K).termResult (.forget A))
        (.cons (deriveList (.substitutionIdentity (sourceContext A))
          (.cons (sourceContextFormed A) .nil)) .nil))))
  change Derivation (signature K) (.term (sourceContext A) (comprehensionTerm A)
    ((objectType (⟨K.ext context A⟩ : Base K) 2).substitute TermExpr.var)) at tree
  rw [objectType_substitute] at tree
  exact tree

theorem comprehension_term_read {context : K.Ctx} (A : K.Ty context) :
    (model K).evaluateTerm (sourceScope A) (comprehensionTerm A) =
      some ⟨forgetType A, forgetValue A⟩ := by
  have read := (model K).evaluate_primitive (sourceScope A) (.forget A)
    TermExpr.var (𝟙 (sourceScope A).1) (by
      intro position
      change (model K).evaluateTerm (sourceScope A) (.var position) =
        some (((sourceScope A).2.lookup position).substitute
          ((NativeModel (Base K)).toCwf.idS (sourceScope A).1))
      rw [Value.substitute_identity]
      rfl)
  change (model K).evaluateTerm (sourceScope A) (comprehensionTerm A) =
    some (Value.substitute (K := (NativeModel (Base K)).toCwf)
      (⟨forgetType A, forgetValue A⟩ : NativeValue (sourceScope A).1)
      (𝟙 (sourceScope A).1)) at read
  exact read.trans (congrArg some
    (Value.substitute_identity (K := (NativeModel (Base K)).toCwf)
      ⟨forgetType A, forgetValue A⟩))

abbrev comprehensionMap {context : K.Ctx} (A : K.Ty context) :
    (sourceScope A).1 ⟶ (objectScope (⟨K.ext context A⟩ : Base K)).1 :=
  RepresentableIndexedDeclarations.forgetMap (displayArrow A)

def dependentBodyType {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) : TypeExpr (symbols K) 2 :=
  sourceType B (comprehensionTerm A)

def dependentBodyMeaning {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) : NativeType (sourceScope A).1 :=
  (sourceMeaning B).reindex (comprehensionMap A)

def dependentBodyFormed {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    Derivation (signature K) (.type (sourceContext A) (dependentBodyType A B)) :=
  deriveList (.typeFamily (sourceContext A) (.source B)
    (singletonArgument (comprehensionTerm A)))
    (.cons (sourceContextFormed A) (.cons (objectContextFormed _)
      (.cons (objectArguments _ (sourceContextFormed A) (comprehensionTermFormed A)) .nil)))

theorem dependent_body_read {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (model K).evaluateType (sourceScope A) (dependentBodyType A B) =
      some (dependentBodyMeaning A B) := by
  exact (model K).evaluate_family (sourceScope A) (.source B)
    (singletonArgument (comprehensionTerm A)) (comprehensionMap A) (by
      intro position
      cases position using Fin.cases with
      | zero =>
        exact (comprehension_term_read A).trans
          (congrArg some (RepresentableIndexedDeclarations.forgetMap_component
            (displayArrow A))).symm
      | succ impossible => exact Fin.elim0 impossible)

def generatedSumType {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) : TypeExpr (symbols K) 1 :=
  .sigma (sourceType A (.var 0)) (dependentBodyType A B)

def generatedProductType {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) : TypeExpr (symbols K) 1 :=
  .pi (sourceType A (.var 0)) (dependentBodyType A B)

def generatedSumFormed {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    Derivation (signature K) (.type (objectContext (⟨context⟩ : Base K)) (generatedSumType A B)) :=
  deriveList (.sigmaFormation (objectContext (⟨context⟩ : Base K))
    (sourceType A (.var 0)) (dependentBodyType A B))
    (.cons (sourceTypeFormed A) (.cons (dependentBodyFormed A B) .nil))

def generatedProductFormed {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    Derivation (signature K) (.type (objectContext (⟨context⟩ : Base K)) (generatedProductType A B)) :=
  deriveList (.piFormation (objectContext (⟨context⟩ : Base K))
    (sourceType A (.var 0)) (dependentBodyType A B))
    (.cons (sourceTypeFormed A) (.cons (dependentBodyFormed A B) .nil))

theorem generated_sum_read {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (model K).evaluateType (objectScope (⟨context⟩ : Base K)) (generatedSumType A B) =
      some ((model K).sums.operations.sigma (sourceMeaning A) (dependentBodyMeaning A B)) :=
  (model K).evaluate_sigma _ _ _ _ _ (source_type_read A) (dependent_body_read A B)

theorem generated_product_read {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (model K).evaluateType (objectScope (⟨context⟩ : Base K)) (generatedProductType A B) =
      some ((model K).products.pi (sourceMeaning A) (dependentBodyMeaning A B)) :=
  (model K).evaluate_pi _ _ _ _ _ (source_type_read A) (dependent_body_read A B)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
