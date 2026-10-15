import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComposition

/-!
# Stability of the earned native monotonicity proposition

Predicate inclusion is restricted to its actual assumption subobject.
Monotonicity of the computed local operator then proves the implication at
all generalized elements. Applying this argument to the already earned
hereditary native operator proves the complete monotonicity proposition
after every context substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneStability

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions NativeMonotoneReadout
open NativeMonotoneCertificate NativeMonotoneBaseChange NativeMonotoneComposition

universe u
variable {C : Type u} [Category.{u} C] {P Q R : Cᵒᵖ ⥤ Type u}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem action_body (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : (predicate A).decoded.sections) :
    action A operator (predicateBody A candidate) =
      predicateBody A (applyValue (predicate A) operator candidate) := by
  rw [action, predicateName_body]

theorem inclusion_action_mono (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (first second : (predicate A).decoded.sections)
    (monotone : Monotone (action (A.reindex (inclusionMeaning A first second).ι)
      (weakenOperator A operator (inclusionMeaning A first second).ι))) :
    inclusionMeaning A first second ≤
      inclusionMeaning A (applyValue (predicate A) operator first) (applyValue (predicate A) operator second) := by
  let guard := inclusionMeaning A first second
  have guardTop : guard.preimage guard.ι = ⊤ := by
    ext world value
    exact iff_of_true value.property (by trivial)
  have before : predicateBody (A.reindex guard.ι) (weakenFunction A first guard.ι) ≤
      predicateBody (A.reindex guard.ι) (weakenFunction A second guard.ι) := by
    apply (inclusionMeaning_top_iff _ _ _).mp
    rw [← inclusionMeaning_substitution]
    exact guardTop
  have after := monotone before
  rw [action_body, action_body] at after
  have conclusion : (inclusionMeaning A (applyValue (predicate A) operator first)
      (applyValue (predicate A) operator second)).preimage guard.ι = ⊤ := by
    rw [inclusionMeaning_substitution, operatorApplication_substitution, operatorApplication_substitution]
    exact (inclusionMeaning_top_iff _ _ _).mpr after
  intro world value held
  have allValues : (⟨value,held⟩ : guard.obj world) ∈
      ((inclusionMeaning A (applyValue (predicate A) operator first)
        (applyValue (predicate A) operator second)).preimage guard.ι).obj world := by
    rw [conclusion]
    trivial
  exact allValues

theorem staged_operator_monotone (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (hereditary : ∀ {X : Cᵒᵖ ⥤ Type u} (map : X ⟶ P),
      Monotone (action (A.reindex map) (weakenOperator A operator map)))
    (substitution : Q ⟶ P) (B : NativeType Q) (localOperator : (operatorType B).decoded.sections)
    (carrier : B = A.reindex substitution)
    (readout : (⟨operatorType B,localOperator⟩ : NativeValue Q) =
      ⟨operatorType (A.reindex substitution),weakenOperator A operator substitution⟩)
    (later : R ⟶ Q) :
    Monotone (action (B.reindex later) (weakenOperator B localOperator later)) := by
  cases carrier
  have sections := eq_of_heq (Sigma.mk.inj readout).2
  rw [sections]
  apply operator_monotone_values_equal (LocalType.reindex_comp A substitution later).symm
  · exact weakenOperator_composition A operator substitution later
  · exact hereditary (later ≫ substitution)

theorem monotonicityMeaning_of_hereditary (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (hereditary : ∀ {X : Cᵒᵖ ⥤ Type u} (map : X ⟶ P),
      Monotone (action (A.reindex map) (weakenOperator A operator map))) :
    monotonicityMeaning A operator = ⊤ := by
  have body : monotonicityBody A operator = ⊤ := by
    rw [monotonicityBody, himp_eq_top_iff]
    apply inclusion_action_mono
    apply staged_operator_monotone A operator hereditary
      (totalProjection (predicate (argumentType A)).decoded ≫ totalProjection (predicate A).decoded)
    · exact (LocalType.reindex_comp A (totalProjection (predicate A).decoded)
        (totalProjection (predicate (argumentType A)).decoded)).symm
    · exact weakenOperator_composition A operator (totalProjection (predicate A).decoded)
        (totalProjection (predicate (argumentType A)).decoded)
  rw [monotonicityMeaning, body, forallAlong_top, forallAlong_top]

theorem checked_monotonicity_reindex (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    monotonicityMeaning (A.reindex substitution) (weakenOperator A operator substitution) = ⊤ := by
  apply monotonicityMeaning_of_hereditary
  intro X later
  exact twice_operator_monotone A operator certified substitution later

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneStability
