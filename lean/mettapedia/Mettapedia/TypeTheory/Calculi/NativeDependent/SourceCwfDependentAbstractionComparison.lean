import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfDependentAbstraction

/-!
# Generated abstraction agrees with its original source certificate

The independently parsed dependent lambda is compared with the original
source function through the complete family comparison. Decoding and
substitution commute with abstraction, so the comparison retains every
future argument and the whole dependent body.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafPiSubstitution ContextualProductSections

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

private theorem abstraction_family_equality
    {C : Type u} [Category.{u} C]
    {P : Mettapedia.Computability.ComputationalTrinity.Face.{u, u, u} C}
    (A : DisplayedFamily.{u, u, u, u} P)
    {B0 B1 : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    (same : B0 = B1) (body0 : B0.sections) (body1 : B1.sections)
    (bodySame : HEq body0 body1) :
    (Functor.sectionsFunctor P.Elements).map
      (eqToIso (congrArg (piDisplayed A) same)).hom (lamDisplayed body0) =
        lamDisplayed body1 := by
  cases same
  cases eq_of_heq bodySame
  rfl

theorem sourceProductTermEquiv_decode (products : StableProducts K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A))
    (function : K.Tm context (products.operations.pi A B)) :
    (Functor.sectionsFunctor _).map (generatedProductMeaning_decode A B).hom
      (sourceProductTermEquiv products A B function) =
        reindexDisplayedSection (objectName (⟨context⟩ : Base K))
          (CwfYoneda.representedProductFamily K A B)
          (CwfYoneda.interpretFunction K products function) := by
  let sections := Functor.sectionsFunctor (objectScope (⟨context⟩ : Base K)).1.Elements
  let comparison := Functor.isoWhiskerLeft (objectName (⟨context⟩ : Base K)).mapElements
    (CwfYoneda.productFamilyIso K products A B)
  have cancel : (sourceProductComparison products A B).hom ≫
      (generatedProductMeaning_decode A B).hom = comparison.hom := by
    simp [sourceProductComparison, comparison]
  change sections.map (generatedProductMeaning_decode A B).hom
    (sections.map (sourceProductComparison products A B).hom (sourceValue function)) = _
  calc
    _ = sections.map ((sourceProductComparison products A B).hom ≫
        (generatedProductMeaning_decode A B).hom) (sourceValue function) := by
      rw [Functor.map_comp]
      rfl
    _ = sections.map comparison.hom (sourceValue function) :=
      congrArg (fun arrow => sections.map arrow (sourceValue function)) cancel
    _ = _ := by
      apply (Functor.sections_ext_iff).2
      intro point
      exact congrArg (fun sectionValue => sectionValue.val
        ((objectName (⟨context⟩ : Base K)).mapElements.obj point))
        (CwfYoneda.productFamilyIso_section K products A B function)

theorem generated_abstraction_decode {context : K.Ctx} {A : K.Ty context}
    {B : K.Ty (K.ext context A)} (body : K.Tm (K.ext context A) B) :
    (Functor.sectionsFunctor _).map (generatedProductMeaning_decode A B).hom
      (NativeLocalTypeOperations.lam (A := sourceMeaning A) (B := dependentBodyMeaning A B)
        (dependentBodyValue body)) =
      reindexDisplayedSection (objectName (⟨context⟩ : Base K))
        (CwfYoneda.representedProductFamily K A B)
        (lamDisplayed (CwfYoneda.representedBodySection K (A := A)
          (CwfYoneda.interpretTerm K body))) := by
  let sections := Functor.sectionsFunctor (objectScope (⟨context⟩ : Base K)).1.Elements
  have decoded := NativeLocalTypeDecoding.abstraction_comparison
    (sourceMeaning A) (dependentBodyMeaning A B) (dependentBodyValue body)
  have castBody := abstraction_family_equality (sourceFamily A) (dependentBodyMeaning_decode A B)
    (dependentBodyValue body)
    (reindexDisplayedSection
      (totalReindexMap (objectName (⟨context⟩ : Base K)) (CwfYoneda.family K A))
      (CwfYoneda.dependentBodyFamily K A B)
      (CwfYoneda.representedBodySection K (A := A) (CwfYoneda.interpretTerm K body)))
    (dependent_body_value_complete body)
  have substituted := lam_substitution_section (objectName (⟨context⟩ : Base K))
    (CwfYoneda.family K A) (CwfYoneda.dependentBodyFamily K A B)
    (CwfYoneda.representedBodySection K (A := A) (CwfYoneda.interpretTerm K body))
  unfold generatedProductMeaning_decode
  simp only [Iso.trans_hom, Functor.map_comp, types_comp_apply]
  exact (congrArg (fun functionValue :
      (piDisplayed (sourceFamily A) (dependentBodyMeaning A B).decoded).sections =>
        sections.map (piSubstitutionIso (objectName (⟨context⟩ : Base K))
          (CwfYoneda.family K A) (CwfYoneda.dependentBodyFamily K A B)).hom
          (sections.map (eqToIso
            (congrArg (piDisplayed (sourceFamily A)) (dependentBodyMeaning_decode A B))).hom
            functionValue)) decoded).trans
    ((congrArg (fun functionValue =>
      sections.map (piSubstitutionIso (objectName (⟨context⟩ : Base K))
        (CwfYoneda.family K A) (CwfYoneda.dependentBodyFamily K A B)).hom functionValue)
      castBody).trans substituted)

/-- The actual generated lambda carries exactly the original source function. -/
theorem sourceProductTermEquiv_abstraction (products : StableProducts K) {context : K.Ctx}
    {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) :
    sourceProductTermEquiv products A B (products.operations.lam body) =
      (model K).products.lam (dependentBodyValue body) := by
  apply (((Functor.sectionsFunctor _).mapIso
    (generatedProductMeaning_decode A B)).toEquiv).injective
  change (Functor.sectionsFunctor _).map (generatedProductMeaning_decode A B).hom
      (sourceProductTermEquiv products A B (products.operations.lam body)) =
    (Functor.sectionsFunctor _).map (generatedProductMeaning_decode A B).hom
      (NativeLocalTypeOperations.lam (dependentBodyValue body))
  rw [sourceProductTermEquiv_decode, CwfYoneda.interpretFunction_lam]
  exact (generated_abstraction_decode body).symm

theorem dependent_lambda_source_read (products : StableProducts K) {context : K.Ctx}
    {A : K.Ty context} {B : K.Ty (K.ext context A)}
    (body : K.Tm (K.ext context A) B) :
    (model K).evaluateTerm (objectScope (⟨context⟩ : Base K)) (dependentLambdaTerm body) =
      some ⟨generatedProductMeaning A B,
        sourceProductTermEquiv products A B (products.operations.lam body)⟩ := by
  rw [dependent_lambda_read, sourceProductTermEquiv_abstraction]

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
