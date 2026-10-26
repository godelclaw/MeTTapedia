import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation

/-!
# Interpretation of individual HOL Light inference operations

Each of the ten original operations preserves translated sequent provability
in a variable-free, substitution-closed background. Ordered premise proofs and
licensed axiom commitments are explicit. Transitivity retains its two source
hypothesis sets, while the original beta adapter supplies its axiom-free proof.
The construction interprets actual source inference semantics; model construction
for chronological declaration replay is a separate consumer.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.InferenceInterpretation
open Mettapedia.Languages.OpenTheory Mettapedia.Logic

variable {theory : HOL.ClosedTheorySet Symbol}

private theorem primitive (background : VariableFreeSubstitutionClosed theory)
    {request : PrimitiveRequest} {out : Theorem} (step : PrimitiveStep request out)
    (premises : ∀ input ∈ request.premises, TranslatedProvable theory input.sequent)
    (axioms : ∀ tagged ∈ out.axioms, TranslatedProvable theory tagged) :
    TranslatedProvable theory out.sequent := by
  obtain ⟨evidence⟩ := step
  exact (translatedProvable_iff_compositionallyProvable _ _).mpr
    (evidence.compositionallyProvable background
      (fun input member _ => (translatedProvable_iff_compositionallyProvable _ _).mp (premises input member))
      (fun tagged member => (translatedProvable_iff_compositionallyProvable _ _).mp (axioms tagged member)))

private theorem core {request : CoreRequest} {out : Theorem}
    (step : CoreStep request out) : PrimitiveStep (.core request) out := by
  obtain ⟨evidence⟩ := step
  exact ⟨.core evidence⟩

private theorem binding {request : BindingRequest} {out : Theorem}
    (step : BindingStep request out) : PrimitiveStep (.binding request) out := by
  obtain ⟨evidence⟩ := step
  exact ⟨.binding evidence⟩

theorem trans {left right out : Theorem}
    (step : TransSemantics left right out)
    (leftProof : TranslatedProvable theory left.sequent)
    (rightProof : TranslatedProvable theory right.sequent) :
    TranslatedProvable theory out.sequent := by
  obtain ⟨first,middle,middle',last,equality,leftView,rightView,same,construction,parts⟩ := step
  subst middle'
  have left := (translatedProvable_iff_compositionallyProvable _ _).mp leftProof
  have right := (translatedProvable_iff_compositionallyProvable _ _).mp rightProof
  obtain ⟨leftFormula,leftTranslated,leftProven⟩ := left
  obtain ⟨type,firstValue,middleValue,typeEqual,firstTranslated,middleTranslated,rfl⟩ :=
    (leftTranslated.of_term_eq leftView.2).equalityDB_inv
  obtain ⟨rightFormula,rightTranslated,rightProven⟩ := right
  obtain ⟨rightType,middleValue',lastValue,rightTypeEqual,middleTranslated',lastTranslated,rfl⟩ :=
    (rightTranslated.of_term_eq rightView.2).equalityDB_inv
  obtain ⟨rfl,sameMiddle⟩ := middleTranslated.unique middleTranslated'
  cases sameMiddle
  apply (translatedProvable_iff_compositionallyProvable _ _).mpr
  refine ⟨_,(TranslatesCompositionally.equalityDB typeEqual firstTranslated lastTranslated).of_term_eq
    ((congrArg CanonicalTerm.term parts.2.2).trans construction.2).symm,?_⟩
  rw [parts.2.1]
  apply provable_equalityLambda_iff.mpr
  refine provable_of_extDerivation (premises := [.eq firstValue middleValue,.eq middleValue lastValue])
    (HOL.ExtDerivation.eqTrans (u := middleValue) (.hyp (by simp)) (.hyp (by simp))) ?_
  intro formula member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact provable_union_left Finset.subset_union_left (provable_equalityLambda_iff.mp leftProven)
  · exact provable_union_left Finset.subset_union_right (provable_equalityLambda_iff.mp rightProven)

theorem inference (background : VariableFreeSubstitutionClosed theory)
    {request : InferenceRequest} {out : Theorem} (step : request.Semantics out)
    (premises : ∀ input ∈ request.premises, TranslatedProvable theory input.sequent)
    (axioms : ∀ tagged ∈ out.axioms, TranslatedProvable theory tagged) :
    TranslatedProvable theory out.sequent := by
  cases request with
  | trans left right =>
      exact trans step (premises left (by simp [InferenceRequest.premises]))
        (premises right (by simp [InferenceRequest.premises]))
  | beta term =>
    have derived := SourceBetaSemantics.derivation_preservation emptyAxiomPolicy step
    obtain ⟨formula,translated,proven⟩ := derives_translatedProvable_of_emptyAxiomPolicy derived
    exact ⟨formula,translated,HOL.ClosedTheorySet.provable_mono
      (by rintro sentence (impossible | member)
          · exact absurd impossible (Set.notMem_empty _)
          · exact Or.inr member) proven⟩
  | refl term => exact primitive background (core ((reflSemantics_iff_coreStep _ _).mp step)) premises axioms
  | assume term => exact primitive background (core ((assumeSemantics_iff_coreStep _ _).mp step)) premises axioms
  | mkComb left right => exact primitive background (core ((appSemantics_iff_coreStep _ _ _).mp step)) premises axioms
  | abs binder input => exact primitive background (binding ((absSemantics_iff_bindingStep _ _ _).mp step)) premises axioms
  | eqMp equality premise => exact primitive background (core ((eqMpSemantics_iff_coreStep _ _ _).mp step)) premises axioms
  | deductAntisym left right => exact primitive background (core ((deductAntisymSemantics_iff_coreStep _ _ _).mp step)) premises axioms
  | instType entries input => exact primitive background ⟨.subst step⟩ premises axioms
  | inst entries input =>
    obtain ⟨substitution,_,substitutionStep⟩ := step
    exact primitive background ⟨.subst substitutionStep⟩ premises axioms

#print axioms trans
#print axioms inference
end Mettapedia.Languages.HOLLight.InferenceInterpretation
