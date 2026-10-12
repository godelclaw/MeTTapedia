import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneBaseChange

/-!
# Composed native operator substitution

Actual native operator values retain the original operator along two
successive substitutions. Hereditary monotonicity and fixed-point transport
therefore apply in the restricted contexts used by induction and coinduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComposition

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions NativeMonotoneReadout
open NativeMonotoneBaseChange

universe u
variable {C : Type u} [Category.{u} C] {P Q R : Cᵒᵖ ⥤ Type u}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem weakenOperator_composition (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (first : Q ⟶ P) (second : R ⟶ Q) :
    (⟨operatorType ((A.reindex first).reindex second),
      weakenOperator (A.reindex first) (weakenOperator A operator first) second⟩ : NativeValue R) =
        ⟨operatorType (A.reindex (second ≫ first)),weakenOperator A operator (second ≫ first)⟩ := by
  have prior := operatorValue_substitution A operator first
  have normalized := operatorValue_substitution (A.reindex first) (weakenOperator A operator first) second
  exact normalized.symm.trans
    ((congrArg (fun value : NativeValue Q => Value.substitute (K := (NativeModel C).toCwf) value second)
      prior.symm).trans
      ((value_substitute_comp _ first second).symm.trans (operatorValue_substitution A operator (second ≫ first))))

theorem operator_monotone_values_equal {before after : NativeType P} (same : before = after)
    (beforeOperator : (operatorType before).decoded.sections)
    (afterOperator : (operatorType after).decoded.sections)
    (values : (⟨operatorType before,beforeOperator⟩ : NativeValue P) = ⟨operatorType after,afterOperator⟩)
    (monotone : Monotone (action after afterOperator)) : Monotone (action before beforeOperator) := by
  cases same
  have sections := eq_of_heq (Sigma.mk.inj values).2
  rw [sections]
  exact monotone

theorem twice_operator_monotone (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (first : Q ⟶ P) (second : R ⟶ Q) :
    Monotone (action ((A.reindex first).reindex second)
      (weakenOperator (A.reindex first) (weakenOperator A operator first) second)) := by
  apply operator_monotone_values_equal (LocalType.reindex_comp A first second).symm
  · exact weakenOperator_composition A operator first second
  · exact reindexed_operator_monotone A operator certified (second ≫ first)

noncomputable def operatorAtTwice (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (first : Q ⟶ P) (second : R ⟶ Q) :
    Subfunctor (totalSpace ((A.reindex first).reindex second).decoded) →o
      Subfunctor (totalSpace ((A.reindex first).reindex second).decoded) where
  toFun := action ((A.reindex first).reindex second)
    (weakenOperator (A.reindex first) (weakenOperator A operator first) second)
  monotone' := twice_operator_monotone A operator certified first second

theorem least_local_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (first : Q ⟶ P) (second : R ⟶ Q) :
    (NativeFixedPointEncodings.leastEncoding (operatorAt A operator certified first)).preimage
      (totalReindexMap second (A.reindex first).decoded) =
        NativeFixedPointEncodings.leastEncoding (operatorAtTwice A operator certified first second) :=
  NativeFixedPointEncodings.least_preimage _ _ _
    (action_substitution (A.reindex first) (weakenOperator A operator first) · second)

theorem greatest_local_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (first : Q ⟶ P) (second : R ⟶ Q) :
    (NativeFixedPointEncodings.greatestEncoding (operatorAt A operator certified first)).preimage
      (totalReindexMap second (A.reindex first).decoded) =
        NativeFixedPointEncodings.greatestEncoding (operatorAtTwice A operator certified first second) :=
  NativeFixedPointEncodings.greatest_preimage _ _ _
    (action_substitution (A.reindex first) (weakenOperator A operator first) · second)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComposition
