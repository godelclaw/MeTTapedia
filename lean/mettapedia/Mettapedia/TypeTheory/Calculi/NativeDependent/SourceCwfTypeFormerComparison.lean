import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfComprehensionBody
import Mettapedia.TypeTheory.CwfYonedaProductSectionComparison

/-!
# Generated dependent formers recover their original source families

The independently generated sum and product expressions decode to the
original source formers through complete natural family isomorphisms.
The body's actual comprehension map earns the comparison. Products keep
the canonical comparison of chosen right-Kan representatives rather than
assuming strict equality of function families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafPiSubstitution DisplayedPresheafSigma
open ContextualProductSections ContextualSumComprehension

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

theorem comprehension_name {context : K.Ctx} (A : K.Ty context) :
    comprehensionMap A ≫ objectName (⟨K.ext context A⟩ : Base K) =
      totalReindexMap (objectName (⟨context⟩ : Base K)) (CwfYoneda.family K A) ≫
        (CwfYoneda.comprehensionIso K A).hom := by
  ext world value
  rfl

theorem dependentBodyMeaning_decode {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (dependentBodyMeaning A B).decoded =
      reindexDisplayed (totalReindexMap (objectName (⟨context⟩ : Base K))
        (CwfYoneda.family K A)) (CwfYoneda.dependentBodyFamily K A B) := by
  change reindexDisplayed (comprehensionMap A ≫ objectName (⟨K.ext context A⟩ : Base K))
      (CwfYoneda.family K B) =
    reindexDisplayed
      (totalReindexMap (objectName (⟨context⟩ : Base K)) (CwfYoneda.family K A) ≫
        (CwfYoneda.comprehensionIso K A).hom) (CwfYoneda.family K B)
  exact congrArg (fun name => reindexDisplayed name (CwfYoneda.family K B))
    (comprehension_name A)

def generatedSumMeaning {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) : NativeType (objectScope (⟨context⟩ : Base K)).1 :=
  sigma (sourceMeaning A) (dependentBodyMeaning A B)

def generatedProductMeaning {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) : NativeType (objectScope (⟨context⟩ : Base K)).1 :=
  pi (sourceMeaning A) (dependentBodyMeaning A B)

theorem generatedSumMeaning_decode {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (generatedSumMeaning A B).decoded =
      reindexDisplayed (objectName (⟨context⟩ : Base K))
        (CwfYoneda.representedSumFamily K A B) := by
  rw [generatedSumMeaning, sigmaDecode, dependentBodyMeaning_decode]
  exact (sigmaDisplayed_reindex (objectName (⟨context⟩ : Base K))
    (CwfYoneda.family K A) (CwfYoneda.dependentBodyFamily K A B)).symm

def generatedProductMeaning_decode {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (show DisplayedFamily (objectScope (⟨context⟩ : Base K)).1 from
      (generatedProductMeaning A B).decoded) ≅
      reindexDisplayed (objectName (⟨context⟩ : Base K))
        (CwfYoneda.representedProductFamily K A B) :=
  piDecodeIso (sourceMeaning A) (dependentBodyMeaning A B) ≪≫
    eqToIso (congrArg (piDisplayed (sourceFamily A)) (dependentBodyMeaning_decode A B)) ≪≫
      piSubstitutionIso (objectName (⟨context⟩ : Base K))
        (CwfYoneda.family K A) (CwfYoneda.dependentBodyFamily K A B)

/-- Whole generated sum families retain both original dependent witnesses. -/
def sourceSumComparison (sums : StableSums K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A)) :
    sourceFamily (sums.operations.sigma A B) ≅ (generatedSumMeaning A B).decoded :=
  Functor.isoWhiskerLeft (objectName (⟨context⟩ : Base K)).mapElements
    (CwfYoneda.sumFamilyIso K sums A B) ≪≫
      eqToIso (generatedSumMeaning_decode A B).symm

/-- Every native generated function fibre has exactly one original source
function fibre, including all future arguments and restrictions. -/
def sourceProductComparison (products : StableProducts K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A)) :
    sourceFamily (products.operations.pi A B) ≅ (generatedProductMeaning A B).decoded :=
  Functor.isoWhiskerLeft (objectName (⟨context⟩ : Base K)).mapElements
    (CwfYoneda.productFamilyIso K products A B) ≪≫
      (generatedProductMeaning_decode A B).symm

theorem generated_sum_family_read {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (model K).evaluateType (objectScope (⟨context⟩ : Base K)) (generatedSumType A B) =
      some (generatedSumMeaning A B) := generated_sum_read A B

theorem generated_product_family_read {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (model K).evaluateType (objectScope (⟨context⟩ : Base K)) (generatedProductType A B) =
      some (generatedProductMeaning A B) := generated_product_read A B

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
