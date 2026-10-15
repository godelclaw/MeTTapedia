import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfTypeFormerTerms

/-!
# Complete generated sums decode to the original witness pairs

The independently formed generated sum family carries every original sum
section. Its canonical decoder agrees with the original complete sum
comparison, through every substituted environment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualSumComprehension

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def generatedSumMeaning_decodeIso {context : K.Ctx} (A : K.Ty context)
    (B : K.Ty (K.ext context A)) :
    (show DisplayedFamily (objectScope (⟨context⟩ : Base K)).1 from
      (generatedSumMeaning A B).decoded) ≅
        reindexDisplayed (objectName (⟨context⟩ : Base K))
          (CwfYoneda.representedSumFamily K A B) :=
  eqToIso (C := DisplayedFamily (objectScope (⟨context⟩ : Base K)).1)
    (generatedSumMeaning_decode A B)

theorem sourceSumTermEquiv_decode (sums : StableSums K) {context : K.Ctx}
    (A : K.Ty context) (B : K.Ty (K.ext context A))
    (term : K.Tm context (sums.operations.sigma A B)) :
    (Functor.sectionsFunctor _).map (generatedSumMeaning_decodeIso A B).hom
      (sourceSumTermEquiv sums A B term) =
        reindexDisplayedSection (objectName (⟨context⟩ : Base K))
          (CwfYoneda.representedSumFamily K A B)
          ((Functor.sectionsFunctor _).map (CwfYoneda.sumFamilyIso K sums A B).hom
            (CwfYoneda.interpretTerm K term)) := by
  let sections := Functor.sectionsFunctor (objectScope (⟨context⟩ : Base K)).1.Elements
  let comparison := Functor.isoWhiskerLeft (objectName (⟨context⟩ : Base K)).mapElements
    (CwfYoneda.sumFamilyIso K sums A B)
  have cancel : (sourceSumComparison sums A B).hom ≫
      (generatedSumMeaning_decodeIso A B).hom = comparison.hom := by
    simp [sourceSumComparison, generatedSumMeaning_decodeIso, comparison]
  change sections.map (generatedSumMeaning_decodeIso A B).hom
    (sections.map (sourceSumComparison sums A B).hom (sourceValue term)) = _
  calc
    _ = sections.map ((sourceSumComparison sums A B).hom ≫
        (generatedSumMeaning_decodeIso A B).hom) (sourceValue term) := by
      rw [Functor.map_comp]
      rfl
    _ = sections.map comparison.hom (sourceValue term) :=
      congrArg (fun arrow => sections.map arrow (sourceValue term)) cancel
    _ = _ := by
      apply (Functor.sections_ext_iff).2
      intro point
      rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
