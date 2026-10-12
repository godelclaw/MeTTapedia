import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfTypeFormerComparison

/-!
# Complete generated dependent terms retain unique source origins

The whole-family comparisons act on every natural sum and function section.
Inverting them and the original comprehension equivalence recovers the exact
original term. The recovery is relative to its supplied original type
presentation; equal decoded families do not erase source type codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open ContextualProductSections ContextualSumComprehension

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def sourceSumTermEquiv (sums : StableSums K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A)) :
    K.Tm context (sums.operations.sigma A B) ≃ (generatedSumMeaning A B).decoded.sections :=
  (sourceTermEquiv (sums.operations.sigma A B)).trans
    (((Functor.sectionsFunctor _).mapIso (sourceSumComparison sums A B)).toEquiv)

def sourceProductTermEquiv (products : StableProducts K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A)) :
    K.Tm context (products.operations.pi A B) ≃ (generatedProductMeaning A B).decoded.sections :=
  (sourceTermEquiv (products.operations.pi A B)).trans
    (((Functor.sectionsFunctor _).mapIso (sourceProductComparison products A B)).toEquiv)

theorem complete_generated_sum_unique_origin (sums : StableSums K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A))
    (value : (generatedSumMeaning A B).decoded.sections) :
    ∃! term : K.Tm context (sums.operations.sigma A B), sourceSumTermEquiv sums A B term = value := by
  refine ⟨(sourceSumTermEquiv sums A B).symm value, (sourceSumTermEquiv sums A B).apply_symm_apply value, ?_⟩
  intro term same
  exact (sourceSumTermEquiv sums A B).injective
    (same.trans ((sourceSumTermEquiv sums A B).apply_symm_apply value).symm)

theorem complete_generated_function_unique_origin (products : StableProducts K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A))
    (value : (generatedProductMeaning A B).decoded.sections) :
    ∃! term : K.Tm context (products.operations.pi A B), sourceProductTermEquiv products A B term = value := by
  refine ⟨(sourceProductTermEquiv products A B).symm value,
    (sourceProductTermEquiv products A B).apply_symm_apply value, ?_⟩
  intro term same
  exact (sourceProductTermEquiv products A B).injective
    (same.trans ((sourceProductTermEquiv products A B).apply_symm_apply value).symm)

theorem whole_generated_functions_reflect_source_equality (products : StableProducts K)
    {context : K.Ctx} (A : K.Ty context) (B : K.Ty (K.ext context A))
    (first second : K.Tm context (products.operations.pi A B)) :
    sourceProductTermEquiv products A B first = sourceProductTermEquiv products A B second ↔ first = second :=
  (sourceProductTermEquiv products A B).injective.eq_iff

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
