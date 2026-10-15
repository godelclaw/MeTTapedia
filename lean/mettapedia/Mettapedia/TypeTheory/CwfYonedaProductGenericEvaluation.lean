import Mettapedia.TypeTheory.CwfYonedaProductEvaluation
import Mettapedia.TypeTheory.ContextualComprehensionTypeEquality
import Mettapedia.TypeTheory.ContextualProductSectionTypeEquality

/-!
# Generic evaluation of represented source functions

The original evaluator's complete generic argument map is the selected
two-stage comprehension lift with its canonical equality comparison.
This records the source of the whole function-fibre comparison, including
the actual context changes induced by non-definitional substitution laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualProductSections ContextualProductCellUniqueness
open ContextualTypeOperations ContextualPiEta
open ContextualComprehensionTypeEquality

universe u w w'
variable (C : Cwf.{u, u, w, w'})

theorem functionArgumentTypeEquality (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩) :
    C.tySub A σ =
      C.tySub (C.tySub A (C.wk (products.operations.pi A B))) function.val := by
  have over := function.property
  change C.compS (C.wk (products.operations.pi A B)) function.val = σ at over
  rw [← C.tySub_comp, over]

theorem genericEvaluatorArgumentLift (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩) :
    evaluatorArgumentLift C products A B (genericArgument C A σ).right
        ((family C (products.operations.pi A B)).map (genericArgument C A σ).hom function) =
      C.compS
        (TypeOver.extensionSubstitution function.val
          (C.tySub A (C.wk (products.operations.pi A B))))
        (TypeOver.isoOfValEq (A := ⟨C.tySub A σ⟩)
          (B := ⟨C.tySub (C.tySub A (C.wk (products.operations.pi A B))) function.val⟩)
          (functionArgumentTypeEquality C products A B σ function)).hom.substitution := by
  rcases function with ⟨arrow, over⟩
  change C.Sub Δ (C.ext Γ (products.operations.pi A B)) at arrow
  change C.compS (C.wk (products.operations.pi A B)) arrow = σ at over
  subst σ
  let P := products.operations.pi A B
  let p := C.wk P
  let Aw := C.tySub A p
  let comparison := TypeOver.compositionObjectIso p arrow (⟨A⟩ : TypeOver C Γ)
  change evaluatorArgumentLift C products A B
      (genericArgument C A (C.compS p arrow)).right
      ((family C P).map (genericArgument C A (C.compS p arrow)).hom ⟨arrow, rfl⟩) =
    C.compS (TypeOver.extensionSubstitution arrow Aw) comparison.hom.substitution
  symm
  apply liftArgument_unique C A p _ _ _
  · rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution, C.comp_assoc,
      comparison.hom.over]
    rfl
  · change C.compS (TypeOver.extensionSubstitution p A)
      (C.compS (TypeOver.extensionSubstitution arrow Aw) comparison.hom.substitution) =
        TypeOver.extensionSubstitution (C.compS p arrow) A
    rw [← C.comp_assoc]
    exact TypeOver.compositionObjectIso_hom_lift p arrow ⟨A⟩

theorem genericEvaluatorBody (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩) :
    HEq
      (genericSection products.operations products.substitution.1
        (cast (congrArg (C.Tm Δ) (products.substitution.1 σ A B))
          (decodeTerm C (products.operations.pi A B) σ function)))
      (C.tmSub
        (genericSection products.operations products.substitution.1
          (genericFunction products.operations products.substitution.1 A B))
        (evaluatorArgumentLift C products A B (genericArgument C A σ).right
          ((family C (products.operations.pi A B)).map
            (genericArgument C A σ).hom function))) := by
  let P := products.operations.pi A B
  let p := C.wk P
  let Aw := C.tySub A p
  let lifted := TypeOver.extensionSubstitution p A
  let Bw := C.tySub B lifted
  let g := genericFunction products.operations products.substitution.1 A B
  let reindexed := reindexFunction products.operations products.substitution.1 function.val g
  let laterLift := TypeOver.extensionSubstitution function.val Aw
  let B₁ := C.tySub Bw laterLift
  let χ := TypeOver.isoOfValEq (A := ⟨C.tySub A σ⟩)
    (B := ⟨C.tySub Aw function.val⟩)
    (functionArgumentTypeEquality C products A B σ function)
  have composite : C.compS lifted (C.compS laterLift χ.hom.substitution) =
      TypeOver.extensionSubstitution σ A := by
    rw [← genericEvaluatorArgumentLift]
    exact evaluatorArgumentLift_original C products A B _ _
  have bodyTypes : C.tySub B₁ χ.hom.substitution =
      C.tySub B (TypeOver.extensionSubstitution σ A) := by
    change C.tySub (C.tySub (C.tySub B lifted) laterLift) χ.hom.substitution = _
    rw [← C.tySub_comp, ← C.tySub_comp, composite]
  have codomains : HEq (C.tySub B (TypeOver.extensionSubstitution σ A)) B₁ :=
    (heq_of_eq bodyTypes.symm).trans
      (equality_type_readout (functionArgumentTypeEquality C products A B σ function) B₁)
  have functions : HEq
      (cast (congrArg (C.Tm Δ) (products.substitution.1 σ A B))
        (decodeTerm C P σ function)) reindexed := by
    have original : HEq reindexed (C.tmSub (C.vz P) function.val) :=
      (reindexFunction_heq products.operations products.substitution.1 function.val g).trans
        (TypeOver.tmSub_heq (products.substitution.1 p A B).symm
          (genericFunction_heq products.operations products.substitution.1 A B) function.val)
    exact ((cast_heq _ _).trans (cast_heq _ _)).trans original.symm
  have bodies := genericSection_type_transport products
    (functionArgumentTypeEquality C products A B σ function) codomains functions
  have equalityReading := equality_term_readout
    (functionArgumentTypeEquality C products A B σ function)
    (genericSection products.operations products.substitution.1 reindexed)
  have reindexedBody := genericSection_reindex products function.val g
  have transported := TypeOver.tmSub_heq rfl (heq_of_eq reindexedBody) χ.hom.substitution
  have composed := TypeOver.tmSub_comp_heq
    (genericSection products.operations products.substitution.1 g)
    laterLift χ.hom.substitution
  have result := bodies.trans (equalityReading.symm.trans (transported.trans composed.symm))
  rw [← genericEvaluatorArgumentLift] at result
  exact result

/-- Generic evaluation recovers the independently formed source function
fibre equivalence, including its entire dependent body display map. -/
theorem sourceEvaluationBody_generic (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩) :
    (sourceEvaluationBody C products A B).app (genericArgument C A σ).right
        ((family C (products.operations.pi A B)).map
          (genericArgument C A σ).hom function) =
      sourceFunctionGenericEquiv C products A B σ function := by
  apply Subtype.ext
  change C.compS
    (C.pair (TypeOver.extensionSubstitution (C.wk (products.operations.pi A B)) A) B
      (genericSection products.operations products.substitution.1
        (genericFunction products.operations products.substitution.1 A B)))
    (evaluatorArgumentLift C products A B (genericArgument C A σ).right
      ((family C (products.operations.pi A B)).map (genericArgument C A σ).hom function)) =
    C.pair (TypeOver.extensionSubstitution σ A) B
      (genericSection products.operations products.substitution.1
        (cast (congrArg (C.Tm Δ) (products.substitution.1 σ A B))
          (decodeTerm C (products.operations.pi A B) σ function)))
  apply TypeOver.substitution_ext
  · rw [← C.comp_assoc, C.wk_pair, evaluatorArgumentLift_original, C.wk_pair]
    rfl
  · let ε := evaluation products.operations products.substitution.1 A B
    let κ := evaluatorArgumentLift C products A B (genericArgument C A σ).right
      ((family C (products.operations.pi A B)).map (genericArgument C A σ).hom function)
    have types : C.tySub (C.tySub B (C.wk B)) ε =
        C.tySub B (TypeOver.extensionSubstitution (C.wk (products.operations.pi A B)) A) := by
      rw [← C.tySub_comp, evaluation_projection]
    have left := (TypeOver.tmSub_comp_heq (C.vz B) ε κ).trans
      (TypeOver.tmSub_heq types
        (evaluation_variable products.operations products.substitution.1 A B) κ)
    have right := (heq_of_eq (C.vz_pair (TypeOver.extensionSubstitution σ A) B
      (genericSection products.operations products.substitution.1
        (cast (congrArg (C.Tm Δ) (products.substitution.1 σ A B))
          (decodeTerm C (products.operations.pi A B) σ function))))).trans (cast_heq _ _)
    exact left.trans ((genericEvaluatorBody C products A B σ function).symm.trans right.symm)

end Mettapedia.TypeTheory.CwfYoneda
